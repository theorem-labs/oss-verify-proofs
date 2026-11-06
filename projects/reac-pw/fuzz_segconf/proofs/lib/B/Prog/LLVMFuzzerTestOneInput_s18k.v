(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 768 of its 809 lines of code are new or changed and 412 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of the walk
   of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), segment S09 (K855c8 -> K856f4,
   0x855c8 .. 0x856f0: check_segments and the per-segment loop of nine calls), LLVMFuzzerTestOneInput_s18.v.

   THE FORM: the image-B twin of image A's S09 kit (the image-A G1 walk owner's lib/A/Prog/LLVMFuzzerTestOneInput_s18k.v and the
   point lemmas of its _s18x.v, image A's S09 workspace on image A's build VM, 2026-10-30T18:2xZ), in
   plugin-hostd/fuzz_command's lib/B/Prog shape (origin/ossv/recipes 3abc3740de97):
   - the pure and reader-level lemmas that give the premises of S09's callees (check_segments, reac_segconf_role,
     check_role, reac_segconf_model, check_model, reac_segconf_ignored, check_ignore, reac_segconf_role_file,
     reac_segconf_ignore_file, check_provenance) from the reader and model blocks (sa_rconf, sa_mconf) and from
     SegModel.segconf_agrees: image A's text word for word (no image number in it);
   - s9M, the memory and frame part every point of S09 keeps (K855c8's lt_core, the two blocks, the slots and the
     model states), and its transport (s9M_agree) to a later reader that agrees on the bytes it reads: the image
     [0x10000, kImgEnd), c, m, the frame's header words and shadow but r's byte SH(FR) + 22, and the real frame
     above S1 but the slots 160 and 176, which image B's S09 writes (0x85620, 0x855e4);
   - s9_call: one call of a program callee of S09 at sp = S1 (cl_callS_wide: r = FR + 176, reac_segconf_role's
     out cell, is a byte of the walk's own side-stack frame), from the callee's statement to the next point's s9M.
   Image B's differences from image A's kit: the frame is 352 bytes (s1 = (SP0 - 352) & ~31), the slots of S09
   are LT_LC's with 112 (&r) and 120 (&probe), and the agreement leaves out the slots 160 and 176.
   Statement text and proofs only about the walk's own points: no other function of the binary is proved here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaCall PaDenot
  PaLibF PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================== lists ============================== *)
Lemma s18k_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n i d H.
  - destruct n; cbn [firstn]; destruct i; reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma s18k_nth_skipn : forall {A} (l : list A) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros A l k. revert l. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; [cbn [skipn]; destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma s18k_fld_fld : forall (bs : list byte) k len off n, (off + n <= len)%nat ->
  seg_spec.fld off n (seg_spec.fld k len bs) = seg_spec.fld (k + off) n bs.
Proof.
  intros bs k len off n H. unfold seg_spec.fld.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (len - off)) with n by lia. f_equal. f_equal. lia.
Qed.

Lemma s18k_nth_le : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma s18k_le4_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. rewrite s18k_nth_le by exact Hk. rewrite !Z_to_bv_unsigned.
  unfold le_byte, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (8 * Z.of_nat 4) with 32. change (2 ^ 32) with 4294967296 in *.
  rewrite (Z.mod_small v 18446744073709551616) by lia. rewrite (Z.mod_small v 4294967296) by lia.
  reflexivity.
Qed.

(* ============================== bytes and strings through the reader ============================== *)
Lemma s18k_bytes_fld : forall rd a bs k n, sa_bytes rd a bs -> (k + n <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat k) (seg_spec.fld k n bs).
Proof.
  intros rd a bs k n B Hk i Hi. unfold seg_spec.fld in *. rewrite length_firstn, length_skipn in Hi.
  rewrite s18k_nth_firstn by lia. rewrite s18k_nth_skipn.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. unfold sa_bytes in B. apply B. lia.
Qed.

Lemma s18k_nth_zs : forall f i, (i < length f)%nat -> nth i (seg_spec.zs f) 0 = bv_unsigned (nth i f ZB0).
Proof.
  unfold seg_spec.zs. induction f as [|b f IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [map nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma s18k_strz : forall rd a f cap s, sa_bytes rd a f -> seg_spec.cstr_enc cap s f -> sa_strz rd a s.
Proof.
  intros rd a f cap s B (Lf & Ls & Nn & E). unfold sa_bytes in B. split; [|exact Nn].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite B by lia. f_equal.
  rewrite <- E. rewrite s18k_nth_firstn by lia. rewrite s18k_nth_zs by lia. reflexivity.
Qed.

Lemma s18k_tail : forall rd a bs e, sa_bytes rd a bs -> a <= e -> e + 8 <= a + Z.of_nat (length bs) ->
  sa_tail rd e.
Proof.
  intros rd a bs e B H1 H2 x Hx. unfold sa_bytes in B.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (B _ Hi) as R. rewrite Z2Nat.id in R by lia.
  replace (a + (x - a)) with x in R by lia. rewrite R. discriminate.
Qed.

(* A char[cap] field [k, k + cap) of the bytes bs at a holding s, with 8 bytes of the block after its NUL: the C
   string and its tail. *)
Lemma s18k_fld_str : forall rd a bs k cap s, sa_bytes rd a bs -> (k + cap <= length bs)%nat ->
  seg_spec.cstr_enc cap s (seg_spec.fld k cap bs) -> (k + length s + 8 <= length bs)%nat ->
  sa_str rd (a + Z.of_nat k) s.
Proof.
  intros rd a bs k cap s B Hk E Hl. split.
  - exact (s18k_strz rd _ _ cap s (s18k_bytes_fld rd a bs k cap B Hk) E).
  - apply (s18k_tail rd a bs _ B); lia.
Qed.

(* A u32 field [k, k + 4) of the bytes bs at a: its value as sa_val. *)
Lemma s18k_u32_val : forall rd a bs k v, sa_bytes rd a bs -> (k + 4 <= length bs)%nat ->
  seg_spec.u32_enc v (seg_spec.fld k 4 bs) -> sa_val rd (a + Z.of_nat k) 4 v.
Proof.
  intros rd a bs k v B Hk (Uv & Ue) j Hj.
  pose proof (s18k_bytes_fld rd a bs k 4 B Hk) as Bf. rewrite Ue in Bf. unfold sa_bytes in Bf.
  rewrite Bf by exact Hj. f_equal. exact (s18k_le4_nth v j Uv Hj).
Qed.

(* ============================== the reader's block, struct reac_segconf ============================== *)
Lemma s18k_rfind_go : forall l nm k i, SegModel.r_find_go l nm k = Some i -> (k <= i < k + length l)%nat.
Proof.
  induction l as [|s l IH]; intros nm k i H; cbn [SegModel.r_find_go] in H; [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end;
    [injection H as <-; cbn [length]; lia|].
  apply IH in H. cbn [length]. lia.
Qed.

Lemma s18k_rfind_lt : forall rc nm i, SegModel.r_find rc nm = Some i -> (i < length (SegModel.rc_seg rc))%nat.
Proof. intros rc nm i H. unfold SegModel.r_find in H. apply s18k_rfind_go in H. lia. Qed.

(* A char[cap] field [off, off + cap) of the entry c->seg[i]: its C string with the tail, inside c's block. *)
Lemma s18k_rfield : forall rd c bs i off cap s, sa_bytes rd c bs -> Z.of_nat (length bs) = seg_spec.SEG_C_SIZE ->
  (i < 32)%nat -> (off + cap <= 356)%nat ->
  seg_spec.cstr_enc cap s (seg_spec.fld off cap (seg_spec.fld (356 * i) 356 bs)) ->
  sa_str rd (c + 356 * Z.of_nat i + Z.of_nat off) s /\
  c + 356 * Z.of_nat i + Z.of_nat off + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < cap)%nat.
Proof.
  intros rd c bs i off cap s B L Hi Ho E.
  rewrite s18k_fld_fld in E by lia. unfold seg_spec.SEG_C_SIZE in *.
  pose proof E as (Lf & Ls & _).
  replace (c + 356 * Z.of_nat i + Z.of_nat off) with (c + Z.of_nat (356 * i + off)) by lia.
  split; [apply (s18k_fld_str rd c bs (356 * i + off) cap s B); [lia | exact E | lia]|].
  split; lia.
Qed.

(* ============================== the checks (A1-A3) ============================== *)
Lemma s18k_bytes_ok : forall inp : list byte, Forall (fun b => 0 <= b < 256) (seg_spec.seg_in inp).
Proof.
  intros inp. unfold seg_spec.seg_in, seg_spec.zs. apply Forall_map, Forall_forall. intros b _.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R.
Qed.

Lemma s18k_harness_ok : forall inp : list byte, SegModel.harness_ok (seg_spec.seg_pay inp) = true.
Proof. intros inp. exact (SegModel.segconf_agrees (seg_spec.seg_in inp) (s18k_bytes_ok inp)). Qed.

Lemma s18k_checks_of : forall p, SegModel.harness_ok p = true ->
  SegModel.check_segments (seg_spec.seg_rc (SegModel.run p)) (seg_spec.seg_mc (SegModel.run p))
    (seg_spec.seg_ret (SegModel.run p)) = true /\
  forallb (SegModel.check_seg (seg_spec.seg_rc (SegModel.run p))) (SegModel.mc_seg (seg_spec.seg_mc (SegModel.run p)))
    = true.
Proof.
  intros p H. unfold SegModel.harness_ok in H. revert H. unfold seg_spec.seg_rc, seg_spec.seg_mc, seg_spec.seg_ret.
  destruct (SegModel.run p) as [[c m] ret]. cbn [fst snd]. intros H. cbv beta iota zeta in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H1 H2].
  split; assumption.
Qed.

Lemma s18_harness : forall pl : list byte,
  let p := seg_spec.seg_pay pl in
  SegModel.check_segments (seg_spec.seg_rc (SegModel.run p)) (seg_spec.seg_mc (SegModel.run p)) (seg_spec.seg_ret (SegModel.run p)) = true /\
  forallb (SegModel.check_seg (seg_spec.seg_rc (SegModel.run p))) (SegModel.mc_seg (seg_spec.seg_mc (SegModel.run p))) = true.
Proof. intros pl p. exact (s18k_checks_of p (s18k_harness_ok pl)). Qed.

Lemma s18_check_seg_nth : forall rc l i, forallb (SegModel.check_seg rc) l = true -> (i < length l)%nat ->
  SegModel.check_seg rc (nth i l SegModel.mseg_d) = true.
Proof.
  intros rc l i H Hi. rewrite forallb_forall in H. apply H. apply nth_In. exact Hi.
Qed.

Lemma s18_check_seg_split : forall rc g, SegModel.check_seg rc g = true ->
  (match SegModel.r_role rc (SegModel.ms_name g) with Some r => SegModel.ms_role_set g && (r =? SegModel.ms_role g) | None => negb (SegModel.ms_role_set g) end) = true /\
  SegModel.same_text (SegModel.r_model rc (SegModel.ms_name g)) (if SegModel.ms_model_set g then Some (SegModel.ms_model g) else None) = true /\
  Bool.eqb (SegModel.r_ignored rc (SegModel.ms_name g)) (SegModel.ms_ignore g) = true /\
  SegModel.same_text (SegModel.r_role_file rc (SegModel.ms_name g)) (if SegModel.ms_role_set g then Some (SegModel.ms_role_file g) else None) = true /\
  SegModel.same_text (SegModel.r_ignore_file rc (SegModel.ms_name g)) (if SegModel.ms_ignore_set g then Some (SegModel.ms_ignore_file g) else None) = true.
Proof.
  intros rc g H. unfold SegModel.check_seg in H. cbv zeta in H.
  apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact H5].
Qed.

(* ============================== the model's block, struct mconf (A4) ============================== *)
Lemma s18_mconf_len : forall rd m mc, sa_mconf rd m mc -> (length (SegModel.mc_seg mc) <= 32)%nat.
Proof. intros rd m mc (bs & B & L & L32 & _). exact L32. Qed.

Lemma s18_mconf_n : forall rd m mc, sa_mconf rd m mc ->
  sa_val rd (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg mc))).
Proof.
  intros rd m mc (bs & B & L & L32 & _ & UN & _).
  unfold seg_spec.SEG_M_SIZE in L. unfold seg_spec.fldz in UN. change (Z.to_nat 4) with 4%nat in UN.
  replace (m + seg_spec.MC_N) with (m + Z.of_nat (Z.to_nat seg_spec.MC_N)) by (unfold seg_spec.MC_N; lia).
  apply (s18k_u32_val rd m bs (Z.to_nat seg_spec.MC_N) _ B); [unfold seg_spec.MC_N; lia | exact UN].
Qed.

Lemma s18_mseg : forall rd m mc i, sa_mconf rd m mc -> (i < length (SegModel.mc_seg mc))%nat ->
  sa_mseg rd (seg_spec.mseg_addr m i) (nth i (SegModel.mc_seg mc) SegModel.mseg_d).
Proof.
  intros rd m mc i (bs & B & L & L32 & HS & _) Hi.
  exists (seg_spec.fld (256 * i) 256 bs). split; [|exact (HS i Hi)].
  unfold seg_spec.SEG_M_SIZE in L. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE.
  replace (m + 256 * Z.of_nat i) with (m + Z.of_nat (256 * i)) by lia.
  apply s18k_bytes_fld; [exact B | lia].
Qed.

Lemma s18_mname : forall rd m mc i, sa_mconf rd m mc -> m mod 16 = 0 -> (i < length (SegModel.mc_seg mc))%nat ->
  sa_str rd (seg_spec.mseg_addr m i) (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) /\
  (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) < 16)%nat.
Proof.
  intros rd m mc i (bs & B & L & L32 & HS & _) _ Hi.
  destruct (HS i Hi) as (Lf & En & _).
  unfold seg_spec.SEG_M_SIZE in L.
  rewrite s18k_fld_fld in En by lia. rewrite Nat.add_0_r in En.
  pose proof En as (_ & Ls & _).
  unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE.
  replace (m + 256 * Z.of_nat i) with (m + Z.of_nat (256 * i)) by lia.
  split; [|exact Ls].
  apply (s18k_fld_str rd m bs (256 * i) 16 _ B); [lia | exact En | lia].
Qed.

(* ============================== the reader's block, struct reac_segconf (A5) ============================== *)
Lemma s18_role_rng : forall rd c rc nm v, sa_rconf rd c rc -> SegModel.r_role rc nm = Some v -> 0 <= v < 2 ^ 31.
Proof.
  intros rd c rc nm v (bs & B & L & L32 & HS & _) H. unfold SegModel.r_role in H.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|discriminate].
  destruct (SegModel.rs_role_set (SegModel.r_seg rc i)); [|discriminate]. injection H as <-.
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & ((R1 & _) & R2) & _). unfold SegModel.r_seg. lia.
Qed.

Lemma s18_model_str : forall rd c rc nm, sa_rconf rd c rc -> c mod 16 = 0 -> 0 < c ->
  sa_ostr rd (seg_spec.model_ptr c rc nm) (SegModel.r_model rc nm) /\
  (forall s, SegModel.r_model rc nm = Some s -> c <= seg_spec.model_ptr c rc nm /\
     seg_spec.model_ptr c rc nm + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < 24)%nat).
Proof.
  intros rd c rc nm (bs & B & L & L32 & HS & _) _ Hc.
  unfold seg_spec.model_ptr, SegModel.r_model.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & Em & _).
  unfold SegModel.r_seg.
  lazymatch goal with |- context [if ?b then Some _ else None] => destruct b end;
    [|split; [reflexivity | discriminate]].
  unfold seg_spec.fldz, seg_spec.RS_MODEL in Em.
  change (Z.to_nat 36) with 36%nat in Em. change (Z.to_nat 24) with 24%nat in Em.
  destruct (s18k_rfield rd c bs i 36 24 _ B L ltac:(lia) ltac:(lia) Em) as (Hs & Hb & Hl).
  cbv beta iota. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_MODEL.
  change (Z.of_nat 36) with 36 in Hs, Hb.
  split; [split; [lia | exact Hs]|].
  intros s Es. injection Es as <-. split; [lia|]. split; [exact Hb | exact Hl].
Qed.

Lemma s18_role_file_str : forall rd c rc nm, sa_rconf rd c rc -> c mod 16 = 0 -> 0 < c ->
  sa_ostr rd (seg_spec.role_file_ptr c rc nm) (SegModel.r_role_file rc nm) /\
  (forall s, SegModel.r_role_file rc nm = Some s -> c <= seg_spec.role_file_ptr c rc nm /\
     seg_spec.role_file_ptr c rc nm + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < 96)%nat).
Proof.
  intros rd c rc nm (bs & B & L & L32 & HS & _) _ Hc.
  unfold seg_spec.role_file_ptr, SegModel.r_role_file.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ef & _).
  unfold SegModel.r_seg.
  lazymatch goal with |- context [if ?b then Some _ else None] => destruct b end;
    [|split; [reflexivity | discriminate]].
  unfold seg_spec.fldz, seg_spec.RS_ROLE_FILE in Ef.
  change (Z.to_nat 160) with 160%nat in Ef. change (Z.to_nat 96) with 96%nat in Ef.
  destruct (s18k_rfield rd c bs i 160 96 _ B L ltac:(lia) ltac:(lia) Ef) as (Hs & Hb & Hl).
  cbv beta iota. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_ROLE_FILE.
  change (Z.of_nat 160) with 160 in Hs, Hb.
  split; [split; [lia | exact Hs]|].
  intros s Es. injection Es as <-. split; [lia|]. split; [exact Hb | exact Hl].
Qed.

Lemma s18_ignore_file_str : forall rd c rc nm, sa_rconf rd c rc -> c mod 16 = 0 -> 0 < c ->
  sa_ostr rd (seg_spec.ignore_file_ptr c rc nm) (SegModel.r_ignore_file rc nm) /\
  (forall s, SegModel.r_ignore_file rc nm = Some s -> c <= seg_spec.ignore_file_ptr c rc nm /\
     seg_spec.ignore_file_ptr c rc nm + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < 96)%nat).
Proof.
  intros rd c rc nm (bs & B & L & L32 & HS & _) _ Hc.
  unfold seg_spec.ignore_file_ptr, SegModel.r_ignore_file.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ei & _).
  unfold SegModel.r_seg.
  lazymatch goal with |- context [if ?b then Some _ else None] => destruct b end;
    [|split; [reflexivity | discriminate]].
  unfold seg_spec.fldz, seg_spec.RS_IGNORE_FILE in Ei.
  change (Z.to_nat 256) with 256%nat in Ei. change (Z.to_nat 96) with 96%nat in Ei.
  destruct (s18k_rfield rd c bs i 256 96 _ B L ltac:(lia) ltac:(lia) Ei) as (Hs & Hb & Hl).
  cbv beta iota. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_IGNORE_FILE.
  change (Z.of_nat 256) with 256 in Hs, Hb.
  split; [split; [lia | exact Hs]|].
  intros s Es. injection Es as <-. split; [lia|]. split; [exact Hb | exact Hl].
Qed.

Lemma s18_ptr_rng : forall rd c rc nm, sa_rconf rd c rc -> 0 <= c ->
  0 <= seg_spec.model_ptr c rc nm <= c + seg_spec.SEG_C_SIZE /\
  0 <= seg_spec.role_file_ptr c rc nm <= c + seg_spec.SEG_C_SIZE /\
  0 <= seg_spec.ignore_file_ptr c rc nm <= c + seg_spec.SEG_C_SIZE.
Proof.
  intros rd c rc nm (bs & B & L & L32 & _) Hc.
  unfold seg_spec.model_ptr, seg_spec.role_file_ptr, seg_spec.ignore_file_ptr, seg_spec.rseg_addr,
    seg_spec.RSEG_SIZE, seg_spec.RS_MODEL, seg_spec.RS_ROLE_FILE, seg_spec.RS_IGNORE_FILE, seg_spec.SEG_C_SIZE.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|cbv beta iota; repeat split; lia].
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (SegModel.r_model rc nm), (SegModel.r_role_file rc nm), (SegModel.r_ignore_file rc nm);
    cbv beta iota; repeat split; lia.
Qed.

(* ============================== the shadow facts (A6) ============================== *)
Lemma s18_sa_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' ->
  sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (H0 & H1 & H2 & H3 & H4) Hq Hn Hn'.
  split; [lia|]. split; [lia|]. split.
  { unfold amem_range in *. lia. }
  split.
  { unfold range_addressable in *. intros x Hx. apply H3. lia. }
  intros Hpos. unfold shadow_hull_vis in *. intros s Hs. apply H4; [lia|].
  assert (M : forall a b, a <= b -> shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8).
  { intros a b Hab. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|].
    apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  pose proof (M q q' Hq) as M1. pose proof (M (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
  lia.
Qed.

(* ============================== the frame objects of S09 ============================== *)
(* r in scope: the shadow byte SH(FR) + 22 is 04 between 0x8563c and 0x856b8 *)
Definition LFO_R : lfo := mkLFO false false true false false.

(* ============================== reading a symbolic state back ============================== *)
Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
(* a register that holds an atom (image A's S00 walk's s10_reg_atom) *)
Lemma s9_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros H E ss ms r n HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* the four bytes of a reader as a 4-byte value of the memory (image A's S09 walk's s9_val_of_rd) *)
Lemma s9_val_of_rd : forall H (mem : word -> option byte) a n v,
  sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
(* the bytes of a memory value through the reader *)
Lemma s9_rd_of_val : forall H (mem : word -> option byte) a n v,
  val_mem SEGS (mrestrict H mem) a n v -> sa_val (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold le_byte. apply bv_wrap_small. change (bv_modulus 8) with 256.
apply Z.mod_pos_bound. lia.
Qed.
End rd.
(* a word every byte of which two readers agree on (image A's S01 / S02 walk's lk_word_kept) *)
Lemma s9_rdword_kept : forall (rd rd' : reader) a v, rdword rd a = Some v ->
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd' a = Some v.
Proof. intros rd rd' a v H K. rewrite (rdword_ext rd rd' a) by (intros k Hk; apply K; lia). exact H. Qed.
(* sa_val carried to a reader that agrees on its bytes *)
Lemma s9_val_kept : forall (rd rd' : reader) a n v, sa_val rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> sa_val rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.
(* signed compare of two words below 2 ^ 63 *)
Lemma s9_lts : forall (x y : word), 0 <= bv_unsigned x < 2 ^ 63 -> 0 <= bv_unsigned y < 2 ^ 63 ->
  bv_lts x y = (bv_unsigned x <? bv_unsigned y).
Proof.
intros x y Hx Hy. unfold bv_lts, bv_signed.
rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia). reflexivity.
Qed.
(* m->n's shadow byte, SH(m + 0x2000), is 0: the 8 bytes m + 0x2000 .. m + 0x2007 are addressable (image A's S09
   walk's s9_mn_shadow) *)
Lemma s9_mn_shadow : forall rd m, sa_addr rd m seg_spec.SEG_M_SIZE -> m mod 16 = 0 ->
  rd (shadow_addr (m + seg_spec.MC_N)) = Some 0.
Proof.
intros rd m (_ & _ & _ & HR & _) H16.
destruct (HR (m + seg_spec.MC_N + 7) ltac:(unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE; lia)) as (s & Hs & Hok).
assert (E : shadow_of_addr SHADOW_OFF (m + seg_spec.MC_N + 7) = shadow_addr (m + seg_spec.MC_N)).
{ unfold shadow_of_addr, shadow_addr, seg_spec.MC_N. f_equal. Z.div_mod_to_equations. lia. }
rewrite E in Hs. rewrite Hs. f_equal.
destruct Hok as [-> | (Hm & Hs8)]; [reflexivity|].
exfalso. assert (Hm7 : (m + seg_spec.MC_N + 7) mod 8 = 7) by (unfold seg_spec.MC_N; Z.div_mod_to_equations; lia). lia.
Qed.

(* ============================== the points of S09 ============================== *)
(* the return points and the loop head of S09 (offsets from BASE = 0x84dc0) *)
Definition LO9_CS : Z := 0x818.    (* 0x855d8: check_segments returned *)
Definition LO9_LOOP : Z := 0x870.  (* 0x85630: the head of the per-segment loop, turn i *)
Definition LO9_R1 : Z := 0x898.    (* 0x85658: reac_segconf_role returned *)
Definition LO9_R2 : Z := 0x8a4.    (* 0x85664: check_role returned *)
Definition LO9_R3 : Z := 0x8b0.    (* 0x85670: reac_segconf_model returned *)
Definition LO9_R4 : Z := 0x8b8.    (* 0x85678: check_model returned *)
Definition LO9_R5 : Z := 0x8c4.    (* 0x85684: reac_segconf_ignored returned *)
Definition LO9_R6 : Z := 0x8cc.    (* 0x8568c: check_ignore returned *)
Definition LO9_R7 : Z := 0x8d8.    (* 0x85698: reac_segconf_role_file returned *)
Definition LO9_R8 : Z := 0x8e8.    (* 0x856a8: reac_segconf_ignore_file returned *)
Definition LO9_R9 : Z := 0x8f8.    (* 0x856b8: check_provenance returned *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the slots of S09's points: K855c8's LT_LC and &r, &probe (176 is each point's own) *)
Definition LS9 (cx : lcx) (c m : Z) : list (Z * Z) :=
  LT_LC cx c m ++ [(112, x_fr cx + FO_R); (120, x_fr cx + FO_PROBE)].
(* the memory and frame part every point of S09 keeps: K855c8's facts with r's shadow as o says *)
Definition s9M (cx : lcx) ly S (W : world SEGS) regs mem md k acc (o : lfo) (c m : Z) : Prop :=
  lt_core B MT cx ly S W regs mem md k acc 6 o [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_slots cx (rdW W mem) (LS9 cx c m) /\ lt_cm (rdW W mem) c m (x_run cx).
(* the loop's registers (0x855fc .. 0x8562c): s2 = 256 i, s3 = &m->seg[i], s5 = i, s6 = 33, s7 = 4, s8 = 90,
   s9 = SH(FR), s10 = -8, s11 = c *)
Definition s9R (cx : lcx) (i : nat) (regs : bvmap 5 word) (c m : Z) : Prop :=
  getr regs 18 = w64 (256 * Z.of_nat i) /\ getr regs 19 = w64 (seg_spec.mseg_addr m i) /\
  getr regs 21 = w64 (Z.of_nat i) /\ getr regs 22 = w64 33 /\ getr regs 23 = w64 4 /\ getr regs 24 = w64 90 /\
  getr regs 25 = w64 (x_sh cx) /\ getr regs 26 = w64 (-8) /\ getr regs 27 = w64 c.
(* 176(s1) = SH(m + 0x2000) from 0x855e4 on *)
Definition s9S (cx : lcx) (rd : reader) (m : Z) : Prop :=
  rdword rd (x_s1 cx + 176) = Some (shadow_addr (m + seg_spec.MC_N)).

Lemma s9_base_facts : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx <= x_sp0 cx - LT_FRAME /\
  getr (x_regs cx) 3 = w64 (as_gp B) /\ getr (x_regs cx) 4 = w64 (as_tp B).
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0 in *. unfold LTOI_FRAME_MAX, LT_FRAME.
set (sp := spZ (x_regs cx)) in *.
assert (Hm : 0 <= (sp - 352) mod 32 < 32) by (apply Z.mod_pos_bound; lia).
assert (Hm16 : (sp - 352) mod 32 = 0 \/ (sp - 352) mod 32 = 16).
{ pose proof (Z.div_mod (sp - 352) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp 16 ltac:(lia)) as D2.
  rewrite Hal in D2. lia. }
split; [exact Hal|]. split; [lia|]. split.
{ rewrite Zminus_mod, Z.mod_mod, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
split; [lia|]. split; [exact Hgp | exact Htp].
Qed.

(* the walk's journal at a point of S09 (lt_frame's first conjunct) *)
Definition s9J (cx : lcx) ly S (W : world SEGS) mem md k : Prop :=
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k.

Hypothesis LAWS : AR_laws SEGS B.

(* the class-3 frame at a point: live in S, at frame_addr of the point's layout, 32-aligned, below the ceiling *)
Lemma s9_frame_at : forall cx ly S W mem md k, lt_base B MT cx -> s9J cx ly S W mem md k ->
  AR SEGS B ly S W mem md /\ In (LT_FCLS, x_fpos cx) (frames S) /\ x_fr cx = frame_addr ly LT_FCLS (x_fpos cx) /\
  x_fr cx mod 32 = 0 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512.
Proof.
intros cx ly S W mem md k HB HJ.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : x_fr cx = frame_addr ly LT_FCLS (x_fpos cx)).
{ unfold x_fr, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin) as (Hal & Happ & _).
pose proof (frames_bounds SEGS B LAWS ly S W mem md _ _ HAR Hin) as (H1 & H2 & _).
change (fs_frame_bytes LT_FCLS) with 512 in *.
rewrite <- EF in Hal, Happ, H1, H2. split; [exact HAR|]. split; [exact Hin|]. split; [exact EF|].
split; [exact Hal|]. split; [exact H1|]. split; [exact H2 | exact Happ].
Qed.

(* a live block of an AR state is a harness block: its alignment, its place and its shadow from AR's laws *)
Lemma s9_hblk_AR : forall ly S W mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
  lt_hblk B ly S (rdW W mem) p n.
Proof.
intros ly S W mem md p n HAR Hin Hn.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H16 & H4096 & Hceil & Happ & _).
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hhull).
assert (Er : req_size n = n) by (unfold req_size; replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
rewrite Er in *. pose proof ASAN_CEIL_range as [CR _]. pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
unfold sa_addr. split; [lia|]. split; [unfold ASAN_CEIL in CR; lia|]. split.
{ unfold amem_range. destruct Happ as (_ & [Hl | (Hh1 & Hh2)]); [left | right];
  unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia. }
split; [|intros _; exact Hhull].
exact (range_addressable_of_block SEGS B LAWS ly S W mem md p n p n HAR Hin ltac:(lia) ltac:(rewrite Er; lia)).
Qed.

(* ---- the image facts survive any change that keeps the image's bytes [0x10000, kImgEnd) (image A's S09 walk) ---- *)
Lemma s9_img_bound : forall a, in_img SEGS a -> 0x10000 <= a < kImgEnd.
Proof. intros a H. exact (pa_img_range a H). Qed.
Lemma s9_lit_kept : forall (W W' : world SEGS) mem mem' a s,
  (forall x, 0x10000 <= x < kImgEnd -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros W W' mem mem' a s K (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|split; [exact Hp | split; [exact Hr | exact Hi]]].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr)].
intros i Hl. rewrite K; [exact (Hz i Hl)|].
apply s9_img_bound. refine (proj1 (Hi (a + Z.of_nat i) _)). rewrite length_app in Hl; cbn [length] in Hl. lia.
Qed.
Lemma s9_img_kept : forall cx (W W' : world SEGS) mem mem',
  (forall x, 0x10000 <= x < kImgEnd -> rdW W' mem' x = rdW W mem x) ->
  lt_img B cx (rdW W mem) -> lt_img B cx (rdW W' mem').
Proof.
intros cx W W' mem mem' K (HRO & HIMG & HGI).
split; [|split].
- intros a Hro Ho He. rewrite K; [exact (HRO a Hro Ho He)|].
  destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [apply s9_img_bound; exists sg; split; [exact Hs | exact Hr]|].
  unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
- destruct HIMG as (HM & HMi & HFZ & HRC & HCAT & HCATa & HW & HR & HSSP & HLp & HLt & HLi & HD1 & HD2 & HD3).
  split; [|split; [exact HMi|split; [|split; [|split; [|split; [exact HCATa|split; [|split; [|split]]]]]]]].
  + intros k0 Hk0. rewrite K; [exact (HM k0 Hk0)|]. apply s9_img_bound.
    exact (proj1 (HMi (mod40A + Z.of_nat k0) ltac:(lia))).
  + intros s Hs. destruct (HFZ s Hs) as [H1 H2]. split; [exact (s9_lit_kept W W' mem mem' _ _ K H1) | exact H2].
  + intros s Hs. destruct (HRC s Hs) as [H1 H2]. split; [exact (s9_lit_kept W W' mem mem' _ _ K H1) | exact H2].
  + destruct HCAT as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (s9_lit_kept W W' mem mem' _ _ K Hl)].
    apply (s9_rdword_kept _ _ _ _ Htp). intros x Hx. apply K. apply s9_img_bound. apply (proj1 (Hci x ltac:(
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *; lia))).
  + destruct HW as (Hwp & Hwi & Hrows). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hrows i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (s9_lit_kept W W' mem mem' _ _ K Hl)].
    apply (s9_rdword_kept _ _ _ _ Hwp'). intros x Hx. apply K. apply s9_img_bound. apply (proj1 (Hwi x ltac:(lia))).
  + destruct HR as (Hrp & Hri & Hrows). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k0 Hk0. rewrite K; [exact (Hrows i Hi k0 Hk0)|]. apply s9_img_bound.
    apply (proj1 (Hri (rolesA + 4 * Z.of_nat i + Z.of_nat k0) ltac:(lia))).
  + destruct HSSP as (Hg & g & Hgv). split.
    * apply (s9_rdword_kept _ _ _ _ Hg). intros x Hx. apply K. unfold gotwA, kImgEnd in *. lia.
    * exists g. apply (s9_rdword_kept _ _ _ _ Hgv). intros x Hx. apply K. unfold guardA, kImgEnd in *. lia.
  + split; [exact HLp|]. split; [exact HLt|]. split; [exact HLi|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- intros i Hi. rewrite K; [exact (HGI i Hi)|]. destruct HIMG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLi & _).
  apply s9_img_bound. apply (proj1 (HLi (longlA + LONGL_W + i) ltac:(unfold LONGL_W, LONGL_N in *; lia))).
Qed.

(* ---- the bytes a point of S09 reads, but r's shadow byte SH(FR) + 22, r itself (which s9M does not read) and the
   slots 160 and 176 ---- *)
Definition s9_slotw (cx : lcx) (a : Z) : Prop :=
  x_s1 cx + 160 <= a < x_s1 cx + 168 \/ x_s1 cx + 176 <= a < x_s1 cx + 184.
Definition s9_agree (cx : lcx) (c m : Z) (rd rd' : reader) : Prop :=
  (forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a) /\
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> rd' a = rd a) /\
  (forall a, m <= a < m + seg_spec.SEG_M_SIZE -> rd' a = rd a) /\
  (forall j, 0 <= j < 36 -> j <> 22 -> rd' (x_sh cx + j) = rd (x_sh cx + j)) /\
  (forall j, (0 <= j < 24 \/ LT_FLAGW <= j < LT_FLAGW + 8) -> rd' (x_fr cx + j) = rd (x_fr cx + j)) /\
  (forall a, x_s1 cx <= a < x_sp0 cx -> ~ s9_slotw cx a -> rd' a = rd a).

Hypothesis MTFL : ameter_fs_laws MT.

Lemma s9_LS9_off : forall cx c m o v, In (o, v) (LS9 cx c m) ->
  (16 <= o <= 152 \/ o = 168 \/ 184 <= o <= 216) /\ o mod 8 = 0.
Proof.
intros cx c m o v Hin. unfold LS9, LT_LC in Hin. cbn [app] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; split; [lia | reflexivity]|]). destruct Hin.
Qed.

Lemma s9M_agree : forall cx ly S W regs mem md k acc o o' c m ly2 S2 W2 regs2 mem2 md2,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  s9J cx ly2 S2 W2 mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  s9_agree cx c m (rdW W mem) (rdW W2 mem2) ->
  rdW W2 mem2 (x_sh cx + 22) = Some (if fo_r o' then 4 else 0xf8) ->
  fo_v o' = fo_v o -> fo_label o' = fo_label o -> fo_probe o' = fo_probe o -> fo_n o' = fo_n o ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  (S2 = S \/ exists f, S2 = set_fs f S) ->
  s9M cx ly2 S2 W2 regs2 mem2 md2 k acc o' c m.
Proof.
intros cx ly S W regs mem md k acc o o' c m ly2 S2 W2 regs2 mem2 md2 HB HM HJ2 E2 E3 E4 E8 E9 HAG Hr22 Ev El Ep En HP HS2.
destruct HM as ((HFR & HIMG & HBL & HBUD) & HC & HMb & HSL & HCM).
destruct HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSAV & W0 & W8 & W16 & W504 & W200 & HZS & W184).
destruct HAG as (KI & KC & KM & KS & KF & KK).
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & _ & _).
pose proof HJ2 as (HAR2 & _).
unfold LTOI_FRAME_MAX, LT_FRAME in Hs1.
assert (KW : forall a v, rdword (rdW W mem) a = Some v -> x_s1 cx <= a -> a + 8 <= x_sp0 cx ->
  (a + 8 <= x_s1 cx + 160 \/ x_s1 cx + 168 <= a) -> (a + 8 <= x_s1 cx + 176 \/ x_s1 cx + 184 <= a) ->
  rdword (rdW W2 mem2) a = Some v).
{ intros a v H H1 H2 H3 H4. apply (s9_rdword_kept _ _ _ _ H). intros x Hx. apply KK; [lia|].
  unfold s9_slotw. lia. }
assert (KFW : forall j v, rdword (rdW W mem) (x_fr cx + j) = Some v -> (j = 0 \/ j = 8 \/ j = 16 \/ j = LT_FLAGW) ->
  rdword (rdW W2 mem2) (x_fr cx + j) = Some v).
{ intros j v H Hj. apply (s9_rdword_kept _ _ _ _ H). intros x Hx.
  replace x with (x_fr cx + (x - x_fr cx)) by lia. apply KF. unfold LT_FLAGW in *. lia. }
split; [split; [|split; [|split]]|split; [|split; [|split]]].
- (* lt_frame *)
  split; [exact HJ2|]. split; [rewrite E2; exact R2|].
  split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E8; exact R8|].
  split; [rewrite E9; exact R9|]. split.
  { intros i r Hi. pose proof (proj1 (nth_error_Some LT_SAVED i) ltac:(rewrite Hi; discriminate)) as Hl.
    cbn [length LT_SAVED] in Hl. apply KW; [exact (HSAV i r Hi) | lia | lia | lia | lia]. }
  split; [replace (x_fr cx) with (x_fr cx + 0) by lia; apply KFW; [rewrite Z.add_0_r; exact W0 | lia]|].
  split; [apply KFW; [exact W8 | lia]|]. split; [apply KFW; [exact W16 | lia]|].
  split; [apply KFW; [exact W504 | lia]|]. split; [apply KW; [exact W200 | lia | lia | lia | lia]|].
  split; [|apply KW; [exact W184 | lia | lia | lia | lia]].
  intros i Hi. rewrite lt_fsh_len in Hi.
  destruct (Nat.eq_dec i 22) as [->|Hne].
  + change (Z.of_nat 22) with 22. rewrite Hr22. destruct o' as [[] [] [] [] []]; reflexivity.
  + rewrite KS by lia. rewrite (HZS i ltac:(rewrite lt_fsh_len; exact Hi)). f_equal.
    destruct o as [v1 l1 r1 p1 n1], o' as [v2 l2 r2 p2 n2]. cbn [fo_v fo_label fo_probe fo_n] in *. subst v2 l2 p2 n2.
    destruct v1, l1, r1, r2, p1, n1; cbn [lt_fsh];
    do 36 (destruct i as [|i]; [first [reflexivity | lia] |]); lia.
- exact (s9_img_kept cx W W2 mem mem2 KI HIMG).
- unfold lt_blocks in *. exact (perm_trans HP HBL).
- destruct HBUD as (Hk & Hr & Hkr & Hle & Hacc & Hacr). split; [exact Hk|]. split; [exact Hr|]. split; [exact Hkr|].
  split; [|split; [exact Hacc | exact Hacr]].
  destruct HS2 as [-> | (f & ->)]; [exact Hle | exact (mo_le_set_fs_r MT MTFL _ _ _ _ Hle)].
- destruct HC as (Hin & _). apply (s9_hblk_AR ly2 S2 W2 mem2 md2 c _ HAR2); [|unfold seg_spec.SEG_C_SIZE; lia].
  exact (Permutation_in _ (Permutation_sym HP) Hin).
- destruct HMb as (Hin & _). apply (s9_hblk_AR ly2 S2 W2 mem2 md2 m _ HAR2); [|unfold seg_spec.SEG_M_SIZE; lia].
  exact (Permutation_in _ (Permutation_sym HP) Hin).
- intros o0 v Hin. pose proof (s9_LS9_off cx c m o0 v Hin) as (Ho & _). apply KW; [exact (HSL o0 v Hin) | lia | lia | lia | lia].
- destruct HCM as ((bs & Hbs & Henc) & (bs' & Hbs' & Henc')). split.
  + exists bs. split; [|exact Henc]. intros i Hi. rewrite KC; [exact (Hbs i Hi)|].
    pose proof Henc as (Hlen & _). lia.
  + exists bs'. split; [|exact Henc']. intros i Hi. rewrite KM; [exact (Hbs' i Hi)|].
    pose proof Henc' as (Hlen & _). lia.
Qed.

(* ---- where the bytes of s9_agree lie: below the ceiling or in the harness's own stack frame, never r's shadow
   byte nor r ---- *)
Definition s9_P (cx : lcx) (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ a <> x_sh cx + 22 /\ ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) /\
  (a < alloc_ceiling \/ x_s1 cx <= a).

Lemma s9_blk_frame_apart : forall ly S W mem md p n cid pos a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) -> p <= a < p + req_size n ->
  ~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid).
Proof.
intros ly S W mem md p n cid pos a HAR Hb Hf Ha Hfa.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [HP _].
pose proof (pairwise_In zdisjoint _ (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid) _ _ eq_refl HP
  (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb)
  (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hf)) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD. lia.
Qed.

Lemma s9_classes : forall cx ly S W regs mem md k acc o c m,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  (forall a, 0x10000 <= a < kImgEnd -> s9_P cx a /\ a < alloc_ceiling) /\
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> s9_P cx a /\ a < alloc_ceiling) /\
  (forall a, m <= a < m + seg_spec.SEG_M_SIZE -> s9_P cx a /\ a < alloc_ceiling) /\
  (forall j, 0 <= j < 36 -> j <> 22 -> s9_P cx (x_sh cx + j) /\ x_sh cx + j < alloc_ceiling) /\
  (forall j, (0 <= j < 24 \/ LT_FLAGW <= j < LT_FLAGW + 8) -> s9_P cx (x_fr cx + j) /\ x_fr cx + j < alloc_ceiling) /\
  (forall a, x_s1 cx <= a < x_sp0 cx -> s9_P cx a) /\
  (0 <= x_sh cx + 22 < alloc_ceiling /\ ~ (x_fr cx + FO_R <= x_sh cx + 22 < x_fr cx + FO_R + 4)).
Proof.
intros cx ly S W regs mem md k acc o c m HB HM.
destruct HM as ((HFR & _) & HC & HMb & _).
pose proof HFR as (HJ & _).
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_img_cover ly S md (proj1 (proj2 HAR))) as [IC1 IC2].
assert (Hsh : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
unfold SHADOW_OFF in Hsh.
(* a byte of r is a byte of the frame, apart from the image and from every block *)
assert (Rimg : forall a, x_fr cx + FO_R <= a < x_fr cx + FO_R + 4 -> ~ (0x10000 <= a < kImgEnd)).
{ intros a Ha Hi. destruct (al_client_img _ _ LAWS ly S W mem md a HAR) as [Hn _].
  - right; left. exists LT_FCLS, (x_fpos cx). split; [exact Hin|]. rewrite <- EF.
    change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Ha. lia.
  - apply Hn. unfold in_zr. lia. }
assert (Rblk : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4)).
{ intros p n a Hb Ha Hr. apply (s9_blk_frame_apart ly S W mem md p n LT_FCLS (x_fpos cx) a HAR Hb Hin Ha).
  rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Hr. lia. }
assert (Rsh : forall j, 0 <= j < 36 -> ~ (x_fr cx + FO_R <= x_sh cx + j < x_fr cx + FO_R + 4)).
{ intros j Hj Hr. rewrite Hsh in Hr. unfold FO_R in Hr. destruct Happ as (_ & [Hl | (Hh & _)]);
  unfold kLowShadowBeg, kHighMemBeg in *; lia. }
assert (Hshc : x_sh cx + 36 <= alloc_ceiling) by (rewrite Hsh; lia).
assert (Hshl : 0x7fff8000 <= x_sh cx) by (rewrite Hsh; lia).
destruct HC as (Hcin & Hc4 & _). destruct HMb as (Hmin & Hm4 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & _ & Hcc & Hcapp & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc, Hcapp.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
assert (Rsh22 : forall a, app_addr a -> a <> x_sh cx + 22).
{ intros a [_ [Ha | [Ha _]]] E; rewrite E, Hsh in Ha; unfold kLowShadowBeg, kHighMemBeg in Ha; lia. }
split; [|split; [|split; [|split; [|split; [|split]]]]].
- intros a Ha. split; [|unfold kImgEnd in *; lia]. split; [unfold kImgEnd in *; lia|]. split; [unfold kImgEnd in *; lia|].
  split; [intros Hr; exact (Rimg a Hr Ha) | left; unfold kImgEnd in *; lia].
- intros a Ha. split; [|unfold seg_spec.SEG_C_SIZE in *; lia]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
  split; [apply Rsh22; exact (in_app_addr _ _ a Hcapp Ha)|].
  split; [apply (Rblk c seg_spec.SEG_C_SIZE a Hcin); change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE; lia|].
  left; lia.
- intros a Ha. split; [|unfold seg_spec.SEG_M_SIZE in *; lia]. split; [unfold seg_spec.SEG_M_SIZE in *; lia|].
  split; [apply Rsh22; exact (in_app_addr _ _ a Hmapp Ha)|].
  split; [apply (Rblk m seg_spec.SEG_M_SIZE a Hmin); change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE; lia|].
  left; lia.
- intros j Hj Hne. split; [|lia]. split; [lia|]. split; [lia|]. split; [exact (Rsh j Hj) | left; lia].
- intros j Hj. unfold LT_FLAGW in Hj. split; [|lia]. split; [lia|].
  split; [apply Rsh22; exact (in_app_addr _ _ (x_fr cx + j) Happ ltac:(lia))|]. split; [unfold FO_R; lia | left; lia].
- intros a Ha. split; [lia|]. split; [lia|]. split; [unfold FO_R; lia | right; lia].
- split; [lia | exact (Rsh 22 ltac:(lia))].
Qed.

(* a call that keeps every byte outside its window [S1 - STK1, S1) and outside r: every byte of s9_agree, r's shadow
   byte and the whole real frame above S1 *)
Lemma s9_agree_kept : forall cx ly S W regs mem md k acc o c m regsc W2 mem2 STK1 (E : Z -> Prop),
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  spZ regsc = x_s1 cx -> 0 <= STK1 -> LTOI_FRAME_MAX + STK1 <= STK_LLVMFuzzerTestOneInput ->
  sa_kept SEGS W mem W2 mem2 regsc STK1 E ->
  (forall a, E a -> x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  s9_agree cx c m (rdW W mem) (rdW W2 mem2) /\ rdW W2 mem2 (x_sh cx + 22) = rdW W mem (x_sh cx + 22) /\
  (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a).
Proof.
intros cx ly S W regs mem md k acc o c m regsc W2 mem2 STK1 E HB HM Hsp HS1 HS2 HK HE.
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
assert (KP : forall a, s9_P cx a -> rdW W2 mem2 a = rdW W mem a).
{ intros a (Ha & _ & Hr & Hlo). apply HK; [exact Ha | rewrite Hsp; lia | intros He; exact (Hr (HE a He))]. }
destruct (s9_classes cx ly S W regs mem md k acc o c m HB HM) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
split; [|split; [apply HK; [lia | rewrite Hsp; lia | intros He; exact (P8 (HE _ He))] | intros a Ha; exact (KP a (P6 a Ha))]].
split; [intros a Ha; exact (KP a (proj1 (P1 a Ha)))|]. split; [intros a Ha; exact (KP a (proj1 (P2 a Ha)))|].
split; [intros a Ha; exact (KP a (proj1 (P3 a Ha)))|]. split; [intros j Hj Hn; exact (KP _ (proj1 (P4 j Hj Hn)))|].
split; [intros j Hj; exact (KP _ (proj1 (P5 j Hj))) | intros a Ha _; exact (KP a (P6 a Ha))].
Qed.

(* a run whose only stores are r's shadow byte and r: every byte of s9_agree and the whole real frame above S1 *)
Lemma s9_agree_win : forall cx ly S W regs mem md k acc o c m (W2 : world SEGS) mem2,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 22 -> ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
    rdW W2 mem2 a = rdW W mem a) ->
  s9_agree cx c m (rdW W mem) (rdW W2 mem2) /\ (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a).
Proof.
intros cx ly S W regs mem md k acc o c m W2 mem2 HB HM HK.
assert (KP : forall a, s9_P cx a -> rdW W2 mem2 a = rdW W mem a) by (intros a (Ha & H22 & Hr & _); exact (HK a Ha H22 Hr)).
destruct (s9_classes cx ly S W regs mem md k acc o c m HB HM) as (P1 & P2 & P3 & P4 & P5 & P6 & _).
split; [|intros a Ha; exact (KP a (P6 a Ha))].
split; [intros a Ha; exact (KP a (proj1 (P1 a Ha)))|]. split; [intros a Ha; exact (KP a (proj1 (P2 a Ha)))|].
split; [intros a Ha; exact (KP a (proj1 (P3 a Ha)))|]. split; [intros j Hj Hn; exact (KP _ (proj1 (P4 j Hj Hn)))|].
split; [intros j Hj; exact (KP _ (proj1 (P5 j Hj))) | intros a Ha _; exact (KP a (P6 a Ha))].
Qed.

(* a run whose only stores are the slots 160 and 176: every byte of s9_agree and r's shadow byte *)
Lemma s9_agree_slots : forall cx ly S W regs mem md k acc o c m (W2 : world SEGS) mem2,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s9_slotw cx a -> rdW W2 mem2 a = rdW W mem a) ->
  s9_agree cx c m (rdW W mem) (rdW W2 mem2) /\ rdW W2 mem2 (x_sh cx + 22) = rdW W mem (x_sh cx + 22).
Proof.
intros cx ly S W regs mem md k acc o c m W2 mem2 HB HM HK.
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
assert (KL : forall a, s9_P cx a /\ a < alloc_ceiling -> rdW W2 mem2 a = rdW W mem a).
{ intros a ((Ha & _) & Hc). apply HK; [exact Ha|]. unfold s9_slotw. lia. }
destruct (s9_classes cx ly S W regs mem md k acc o c m HB HM) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
split; [|apply HK; [lia | unfold s9_slotw; lia]].
split; [intros a Ha; exact (KL a (P1 a Ha))|]. split; [intros a Ha; exact (KL a (P2 a Ha))|].
split; [intros a Ha; exact (KL a (P3 a Ha))|]. split; [intros j Hj Hn; exact (KL _ (P4 j Hj Hn))|].
split; [intros j Hj; exact (KL _ (P5 j Hj)) | intros a Ha Hn; apply HK; [lia | exact Hn]].
Qed.

(* r's shadow byte at a point *)
Lemma s9_r_shadow : forall cx ly S W regs mem md k acc o c m, s9M cx ly S W regs mem md k acc o c m ->
  rdW W mem (x_sh cx + 22) = Some (if fo_r o then 4 else 0xf8).
Proof.
intros cx ly S W regs mem md k acc o c m ((HFR & _) & _).
destruct HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HZS & _).
pose proof (HZS 22%nat ltac:(rewrite lt_fsh_len; lia)) as H. change (Z.of_nat 22) with 22 in H. rewrite H.
destruct o as [[] [] [] [] []]; reflexivity.
Qed.

(* a run that stores nothing keeps s9M with the run's registers and model *)
Lemma s9M_run : forall cx ly S W regs mem md k acc o c m regs2 mem2 md2,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m -> s9J cx ly S W mem2 md2 k ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem a) ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  s9M cx ly S W regs2 mem2 md2 k acc o c m.
Proof.
intros cx ly S W regs mem md k acc o c m regs2 mem2 md2 HB HM HJ HK E2 E3 E4 E8 E9.
assert (HKA : forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 22 -> ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  rdW W mem2 a = rdW W mem a) by (intros a Ha _ _; exact (HK a Ha)).
destruct (s9_agree_win cx ly S W regs mem md k acc o c m W mem2 HB HM HKA) as [HAG _].
destruct (s9_classes cx ly S W regs mem md k acc o c m HB HM) as (_ & _ & _ & _ & _ & _ & (H22 & _)).
pose proof asan_consts as (C1 & _).
assert (Hr22 : rdW W mem2 (x_sh cx + 22) = Some (if fo_r o then 4 else 0xf8)).
{ rewrite HK by lia. exact (s9_r_shadow cx ly S W regs mem md k acc o c m HM). }
exact (s9M_agree cx ly S W regs mem md k acc o o c m ly S W regs2 mem2 md2 HB HM HJ E2 E3 E4 E8 E9 HAG Hr22
  eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl)).
Qed.

(* ---- what every call of S09 asks of the caller's frame (cl_callS's premises), at sp = S1 ---- *)
Lemma s9_call_frame : forall cx ly S W regs mem md k acc o c m (regsc : bvmap 5 word),
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  getr regsc 2 = getr regs 2 -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 8 = getr regs 8 ->
  spZ regsc = x_sp0 cx + (x_s1 cx - x_sp0 cx) /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\ x_s1 cx - x_sp0 cx <= 0 /\
  getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  (exists ch, achain ly (rdW W mem) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsc) ch) /\
  arodata_okP SEGS RLO_A RHI_A B (rdW W mem) /\ st_nev S <= EV_MAX /\
  (forall STK1, In STK1 LTOI_CALLEE_STKS -> 0 <= STK1 /\ STK1 - (x_s1 cx - x_sp0 cx) <= STK_LLVMFuzzerTestOneInput).
Proof.
intros cx ly S W regs mem md k acc o c m regsc HB HM E2 E3 E4 E8.
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & Hgp & Htp).
pose proof HB as (_ & HPRES & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _).
destruct HM as ((HFR & (HRO & _) & _ & HBUD) & _).
destruct HFR as (HJ & R2 & R3 & R4 & R8 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HBUD as (Hk & _ & Hkr & _).
pose proof asan_consts as (C1 & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
assert (Hsp : spZ regsc = x_s1 cx).
{ unfold spZ. rewrite E2, R2. apply unsigned_lit_small. lia. }
assert (Hd : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D2.
  rewrite Hs1a in D1. rewrite Hal in D2.
  replace (x_s1 cx - x_sp0 cx) with ((2 * (x_s1 cx / 32) - x_sp0 cx / 16) * 16) by lia. apply Z.mod_mul; lia. }
split; [lia|]. split; [exact Hd|]. split; [lia|].
split; [rewrite E3, R3; exact Hgp|]. split; [rewrite E4, R4; exact Htp|]. split.
- assert (HP : astack_pres ly (w_H W) mem (x_sp0 cx - 32768)).
  { eapply (astack_pres_journal SEGS B pa_segs_low); [exact HJ | exact HPRES |].
    intros a (r & Hr & Ha) Ha2. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
    exfalso. unfold longlA, A_LONGL, LONGL_N, x_sp0 in *. lia. }
  apply achain_any.
  + apply astack_rd_of_pres. apply (astack_pres_mono _ _ _ (x_sp0 cx - 32768)); [lia | exact HP].
  + right; right; right. unfold s0Z. rewrite E8, R8. rewrite unsigned_lit_small by lia. lia.
- split; [exact HRO|]. split; [unfold EV_LTOI in *; lia|].
  intros STK1 Hin. pose proof (ltoi_callee_stks STK1 Hin) as [H1 H2].
  unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in H2. split; lia.
Qed.

(* ---- one call of a program callee of S09 at sp = S1: its statement's post (apost_base, no allocator event, a
   footprint and a written set inside r) gives the next point's s9M, the callee-saved registers, the post's own
   facts R and the real frame above S1 unchanged (cl_callS_wide; r is a byte of the walk's own frame) ---- *)
Lemma s9_call : forall cx ly S W regs mem md k acc o c m (regsc : bvmap 5 word) (pc : Z) STK1 FP1 EV1 (E : Z -> Prop)
  (Q1 R : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) Q,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  getr regsc 2 = getr regs 2 -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 8 = getr regs 8 -> getr regsc 9 = getr regs 9 ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= bv_unsigned (getr regsc 1) ->
  In STK1 LTOI_CALLEE_STKS -> EV1 = 0 ->
  (forall a, inFP FP1 a -> x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  (forall a, E a -> x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  (forall ch, afn_pre SEGS B STK1 ly S W regsc mem md ch -> arodata_okP SEGS RLO_A RHI_A B (rdW W mem) ->
     st_nev S + EV1 <= EV_MAX ->
     SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 pc) mem (seg_rom SEGS)) md)
       (apost_base SEGS B STK1 FP1 regsc ly S W mem md EV1 Q1)) ->
  (forall ly' S' W' regs' mem' md', Q1 ly' S' W' regs' mem' md' ->
     R ly' S' W' regs' mem' md' /\ sa_kept SEGS W mem W' mem' regsc STK1 E /\ sa_noalloc B ly S ly' S') ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     s9M cx ly2 S2 W2 regs2 mem2 md2 k acc o c m -> aregs_preserved regsc regs2 -> R ly2 S2 W2 regs2 mem2 md2 ->
     (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) ->
     (forall a, x_fr cx + FO_R <= a < x_fr cx + FO_R + 4 -> ~ inFP FP1 a -> rdW W2 mem2 a = rdW W mem a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (getr regsc 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 pc) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k acc o c m regsc pc STK1 FP1 EV1 E Q1 R Q HB HM E2 E3 E4 E8 E9 Hra Hra4 HSTK HEV1
  HFP HE HCALLEE HQR HK.
subst EV1.
destruct (s9_call_frame cx ly S W regs mem md k acc o c m regsc HB HM E2 E3 E4 E8)
  as (Hspc & Ho16 & Honeg & P3c & P4c & (ch & Hch) & HRO & Hnev & HSTKS).
destruct (HSTKS STK1 HSTK) as [HS1 HS2].
pose proof HM as ((HFR & _) & _). pose proof HFR as (HJ & _).
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & _ & _).
pose proof asan_consts as (C1 & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsc mem (Z_to_bv 64 pc) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k STK1 FP1 0 (x_s1 cx - x_sp0 cx)
    (getr regsc 1) ch Q1 HJ Hspc Ho16 Honeg HS1 HS2 P3c P4c eq_refl Hra Hra4 Hch).
  - intros HPRE1. exact (HCALLEE ch HPRE1 HRO ltac:(lia)).
  - intros a Ha. pose proof (HFP a Ha) as Hr. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Hr. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFP a Ha) as Hr. unfold FO_R in Hr.
    unfold STK_LLVMFuzzerTestOneInput in Hw. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HQ2).
destruct (HQR _ _ _ _ _ _ HQ2) as (HR2 & HK2 & HNA2).
replace (k + 0) with k in HJ2 by lia.
assert (Hsp' : spZ regsc = x_s1 cx) by (rewrite Hspc; lia).
destruct (s9_agree_kept cx ly S W regs mem md k acc o c m regsc W2 mem2 STK1 E HB HM Hsp' HS1
  ltac:(pose proof (ltoi_callee_stks STK1 HSTK) as [_ Hq]; exact Hq) HK2 HE) as (HAG & H22 & HST).
destruct HNA2 as (HPm & -> & HSf).
pose proof (s9M_agree cx ly S W regs mem md k acc o o c m ly S2 W2 regs2 mem2 md2 HB HM HJ2
  (eq_trans (HP2 2 ltac:(unfold acallee_saved; lia)) E2) (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) E3)
  (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) E4) (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) E8)
  (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) E9) HAG
  ltac:(rewrite H22; exact (s9_r_shadow cx ly S W regs mem md k acc o c m HM))
  eq_refl eq_refl eq_refl eq_refl HPm (or_intror HSf)) as HM2.
assert (KR : forall a, x_fr cx + FO_R <= a < x_fr cx + FO_R + 4 -> ~ inFP FP1 a -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha HnF. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KF & _).
  apply (KF LT_FCLS (x_fpos cx) a Hin); [|exact HnF]. left. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Ha. lia. }
exact (HK ly S2 W2 regs2 mem2 md2 HM2 HP2 HR2 HST KR).
Qed.

End e.
End f.
End d.
