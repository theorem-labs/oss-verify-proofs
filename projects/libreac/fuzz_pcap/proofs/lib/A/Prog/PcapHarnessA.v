(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v, with its module names changed; 2018 of its 2157 lines of code are new or changed and 3418 lines of the source are left out. *)
(* fuzz_pcap's entry function LLVMFuzzerTestOneInput (0x807c8, listing offset 0x90) on the ASan build of
   libreac v1.9.0: the walks of its first part, between the cut pcs of PcapEntryDefs.v, in the form
   PcapEntryPhases.v fixes (`pe_from POST GI_next -> pe_from POST GI_self`, cgif_file_fuzzer's per-function form).

   Walks of this file (PcapEntryDefs.v:217-235):
     B       PP_K2 (0x809a0) -> the harness's check of the open's verdict (0x809a0..0x80aa0) -> accepted: malloc
             0x80ab8 -> PP_K3 (h_B_malloc); refused: free 0x80a84 -> j PP_K12r (h_B_free): pe_B. Every branch to
             PP_abort (0x80a3c / 0x80a40 / 0x80a50 / 0x80a70 / 0x80aa0) is refuted from GI_K2's verdict a0, p_good and
             h_U_K; the four shadow checks of the copy (bnez 0x809c0 / 0x809dc / 0x809f4 / 0x80a0c, slow blocks
             0x81358 / 0x81368 / 0x81378 / 0x81388) are decided by the run's one shadow entry mkSHE 19 0 4 over
             [b, b+4) (hSH_B), discharged in HSgen from AR_shadow_law's block_shadow of the copy b (4 <= p_nF).
     C       PP_K3 (0x80abc) -> pcap_source_next 0x80af0 -> PP_KD (0x80af4): pe_C, with the call and the return in
             h_C_next. Its one branch, beqz 0x80abc to PP_abort, is decided by GI_K3's 4096 <= buf.

   The machine-frame arm (flag 0 at 0x80830, or __asan_stack_malloc_1 returning 0 at 0x8084c) is refuted by
   AR_const_law's use-after-return cell = 1; if the core drops that law, the phase layer gains a frame-location
   parameter.

   Callee statements, as Section hypotheses of their exact type (SK explicit): pcap_source_next,
   tpcap_source_next_specX (lib/A/Prog/PcapSourceNextDefs.v, a Theorem Labs lane); malloc / free, amalloc04_rule /
   afree04_rule (lib/Reusable/YC5d.v, cgif core), through PaJournalFs's amalloc04_sub_fs / afree04_sub_fs.

   Every number is read from the original v1.9.0 pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...; symbols
   from its unstripped twin, capstone disassembly); the comment beside a number names its instruction. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YE01 YG0p YC5d YI13.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 YC88 PcapFrame PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YA0f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module PST := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.

(* ---- the reader's model: a fit record is the last record the chain saw (cf. lib/Prog/Slot/PWalk.v chain_fit,
   re-proved here over the model alone) ---- *)
Section model.
Variables (sw : bool) (F : list byte) (cap : Z).

Lemma h_incl_nonneg : forall q, 0 <= PSN.incl sw F q.
Proof.
  intros q. unfold PSN.incl, PSN.hw, PSN.w32le, PSN.fb.
  repeat match goal with |- context [bv_unsigned ?x] =>
    lazymatch goal with H : 0 <= bv_unsigned x < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 8 x) end end.
  destruct sw; lia.
Qed.

Lemma h_kind_cuth : forall q, PSN.flen F < q -> PSN.kind sw F cap q = PSN.KCutH.
Proof.
  intros q H. unfold PSN.kind.
  destruct (Z.eqb_spec (PSN.flen F - q) 0); [lia|].
  destruct (Z.ltb_spec (PSN.flen F - q) 16); [reflexivity | lia].
Qed.

Lemma h_chain_fit : forall f q lh, PSN.flen F - q < 16 * Z.of_nat f ->
  PSN.kind sw F cap (fst (fst (PSN.chain sw F cap f q lh))) = PSN.KFit ->
  snd (PSN.chain sw F cap f q lh) = Some (fst (fst (PSN.chain sw F cap f q lh))).
Proof.
  induction f as [|f IH]; intros q lh H HK.
  - cbn [PSN.chain fst] in HK. rewrite h_kind_cuth in HK by lia. discriminate.
  - cbn [PSN.chain] in HK |- *. destruct (PSN.kind sw F cap q) eqn:K; cbn [fst snd] in HK |- *;
      try reflexivity; try (rewrite K in HK; discriminate).
    + apply IH; [lia | exact HK].
    + pose proof (h_incl_nonneg q).
      destruct (PSN.chain sw F cap f (q + 16 + PSN.incl sw F q) (Some q)) as [[Q o] l] eqn:EC.
      cbn [fst snd] in HK |- *. specialize (IH (q + 16 + PSN.incl sw F q) (Some q)). rewrite EC in IH.
      apply IH; [lia | exact HK].
Qed.

Lemma h_psn_lh_fit : forall p, 0 <= p -> PSN.kind sw F cap (PSN.psn_q sw F cap p) = PSN.KFit ->
  PSN.psn_lh sw F cap p = Some (PSN.psn_q sw F cap p).
Proof. intros p Hp HK. unfold PSN.psn_lh, PSN.psn_q, PSN.psn_chain in *. apply h_chain_fit; [unfold PSN.flen; lia | exact HK]. Qed.
End model.

Lemma h_bytesZ_unsigned : forall l : list byte, bytesZ (map (fun b : byte => bv_unsigned b) l) = l.
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [map]. unfold bytesZ in *. cbn [map]. rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.


(* The shadow bytes of a frame as one-byte chunks, from offset i on. *)
Fixpoint hsh_chunks (i : Z) (sh : list Z) : list YP09.chunk :=
  match sh with [] => [] | v :: t => YP09.mkChunk i (CVal 1 (SLit v)) :: hsh_chunks (i + 1) t end.

Lemma hsh_chunks_In : forall sh i j, (i < length sh)%nat ->
  In (YP09.mkChunk (j + Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (hsh_chunks j sh).
Proof.
  intros sh. induction sh as [|v t IH]; intros i j Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [hsh_chunks nth].
  - left. rewrite Z.add_0_r. reflexivity.
  - right. replace (j + Z.of_nat (S i)) with (j + 1 + Z.of_nat i) by lia. apply IH. lia.
Qed.


(* ---- the harness's magic test (0x809b4..0x80a3c): four bytes assembled into a sign-extended 32-bit word ---- *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma h_sext24 : forall c, 0 <= c < 256 ->
  bv_wrap 64 (bv_swrap 32 (c * 2 ^ 24)) = c * 2 ^ 24 + (if c <? 128 then 0 else 2 ^ 64 - 2 ^ 32).
Proof.
  intros c Hc. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec c 128); lia.
Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition h_magic_sv : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 34 0)) (SAlu ALU_SLL (SOff 36 0) (SLit 16)))
    (SAluw ALU_SLL (SOff 37 0) (SLit 24)).

Lemma h_magic_U : forall E c0 c1 c2 c3,
  ew E 34 = Z_to_bv 64 c0 -> ew E 35 = Z_to_bv 64 c1 -> ew E 36 = Z_to_bv 64 c2 -> ew E 37 = Z_to_bv 64 c3 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  U E h_magic_sv = c0 + 256 * c1 + 65536 * c2 + 16777216 * c3 + (if c3 <? 128 then 0 else 2 ^ 64 - 2 ^ 32).
Proof.
  intros E c0 c1 c2 c3 E0 E1 E2 E3 H0 H1 H2 H3.
  assert (Uc0 : U E (SOff 34 0) = c0) by (apply U_atom; [exact E0 | lia]).
  assert (Uc1 : U E (SOff 35 0) = c1) by (apply U_atom; [exact E1 | lia]).
  assert (Uc2 : U E (SOff 36 0) = c2) by (apply U_atom; [exact E2 | lia]).
  assert (Uc3 : U E (SOff 37 0) = c3) by (apply U_atom; [exact E3 | lia]).
  assert (T5 : U E (SAluw ALU_SLL (SOff 37 0) (SLit 24)) = c3 * 2 ^ 24 + (if c3 <? 128 then 0 else 2 ^ 64 - 2 ^ 32)).
  { rewrite U_of_S, S_SAluw, Uc3, U_SLit. cbn [zalu_raw]. rewrite (Z.mod_small c3) by lia.
    change (zcanon 24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24. rewrite Z.shiftl_mul_pow2 by lia.
    apply h_sext24. exact H3. }
  unfold h_magic_sv. rewrite !U_SAlu, T5, Uc0, Uc1, Uc2, !U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 8) 63) with 8. change (Z.land (zcanon 16) 63) with 16.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (zcanon_id (c1 * 2 ^ 8)) by (unfold M64; lia). rewrite (zcanon_id (c2 * 2 ^ 16)) by (unfold M64; lia).
  rewrite (YA0f.APSXG.lor_shl_disjoint c1 c0 8) by lia. rewrite (zcanon_id (c1 * 2 ^ 8 + c0)) by (unfold M64; lia).
  rewrite (Z.lor_comm (c1 * 2 ^ 8 + c0)), (YA0f.APSXG.lor_shl_disjoint c2 (c1 * 2 ^ 8 + c0) 16) by lia.
  rewrite (zcanon_id (c2 * 2 ^ 16 + (c1 * 2 ^ 8 + c0))) by (unfold M64; lia).
  rewrite Z.lor_comm.
  destruct (Z.ltb_spec c3 128).
  - rewrite Z.add_0_r, (YA0f.APSXG.lor_shl_disjoint c3 (c2 * 2 ^ 16 + (c1 * 2 ^ 8 + c0)) 24) by lia.
    rewrite zcanon_id by (unfold M64; lia). lia.
  - replace (c3 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32)) with ((c3 + (2 ^ 40 - 2 ^ 8)) * 2 ^ 24) by lia.
    rewrite (YA0f.APSXG.lor_shl_disjoint (c3 + (2 ^ 40 - 2 ^ 8)) (c2 * 2 ^ 16 + (c1 * 2 ^ 8 + c0)) 24) by lia.
    rewrite zcanon_id by (unfold M64; lia). lia.
Qed.



(* ---- the model's magic, as the harness's four bytes ---- *)
Lemma h_bt : forall (F : list byte) i, nth i (map (fun b : byte => bv_unsigned b) F) 0 = PST.pcap_byte F i.
Proof. intros F i. unfold PST.pcap_byte. exact (map_nth (fun b : byte => bv_unsigned b) F (Z_to_bv 8 0) i). Qed.

Lemma h_bt_range : forall (F : list byte) i, 0 <= nth i (map (fun b : byte => bv_unsigned b) F) 0 < 256.
Proof.
  intros F i. rewrite h_bt. unfold PST.pcap_byte.
  pose proof (bv_unsigned_in_range 8 (nth i F (Z_to_bv 8 0))) as R. unfold bv_modulus in R. exact R.
Qed.


Lemma h_sll3 : forall d, 0 <= d < 256 ->
  alu64 ALU_SLL (Z_to_bv 64 d) (Z_to_bv 64 3) = Z_to_bv 64 (8 * d).
Proof.
  intros d Hr. rewrite zalu64_sound. f_equal.
  unfold zalu64, zcanon. rewrite (Z.mod_small d) by (unfold M64; lia). rewrite (Z.mod_small 3) by (unfold M64; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  replace (d * 2 ^ 3) with (8 * d) by lia. apply Z.mod_small. unfold M64. lia.
Qed.

Definition h_K1 : Z := 18446744072127431636.   (* lui 0xa1b2c + addiw 0x3d4 0x80a34: the sign-extended magic *)
Definition h_K2 : Z := 18446744072984179361.   (* lui 0xd4c3b + addiw 0x2a1 0x80a58: the swapped magic *)
Definition h_seqz_sv : sv := SAlu ALU_SLTU (SAlu ALU_XOR h_magic_sv (SLit h_K2)) (SLit 1).

Lemma h_seqz_gen : forall E (v : sv) m, U E v = m ->
  U E (SAlu ALU_SLTU (SAlu ALU_XOR v (SLit h_K2)) (SLit 1)) = (if m =? h_K2 then 1 else 0).
Proof.
  intros E v m HM. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, HM.
  pose proof (U_range E v) as HR. rewrite HM in HR. unfold M64 in HR.
  assert (Hx : 0 <= Z.lxor m h_K2 < 2 ^ 64).
  { apply Z_lxor_range; unfold h_K2; lia. }
  rewrite (zcanon_id (Z.lxor m (zcanon h_K2))) by (rewrite (zcanon_id h_K2) by (unfold M64, h_K2; lia); unfold M64; lia).
  rewrite (zcanon_id h_K2) by (unfold M64, h_K2; lia). rewrite (zcanon_id 1) by (unfold M64; lia).
  destruct (Z.eqb_spec m h_K2) as [->|Hne].
  - rewrite Z.lxor_nilpotent. cbn. apply zcanon_id. unfold M64. lia.
  - assert (Hn0 : Z.lxor m h_K2 <> 0) by (intros Hz; exact (Hne (proj1 (Z.lxor_eq_0_iff m h_K2) Hz))).
    destruct (Z.ltb_spec (Z.lxor m h_K2) 1); [lia|]. apply zcanon_id. unfold M64. lia.
Qed.

Lemma h_seqz_U : forall E m, U E h_magic_sv = m -> U E h_seqz_sv = (if m =? h_K2 then 1 else 0).
Proof. intros E m HM. unfold h_seqz_sv. exact (h_seqz_gen E h_magic_sv m HM). Qed.

Lemma h_a2_U : forall E m, U E h_magic_sv = m ->
  U E (SAlu ALU_ADD h_seqz_sv (SLit (-1))) = (if m =? h_K2 then 0 else 2 ^ 64 - 1).
Proof.
  intros E m HM. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (h_seqz_U E m HM).
  assert (EM1 : zcanon (-1) = 2 ^ 64 - 1) by (vm_compute; reflexivity).
  rewrite EM1. unfold zcanon, M64.
  destruct (Z.eqb_spec m h_K2).
  - replace (1 + (2 ^ 64 - 1)) with (2 ^ 64) by lia. apply Z_mod_same_full.
  - rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.

Lemma h_mv_U : forall E m, U E h_magic_sv = m -> U E (SAlu ALU_ADD h_magic_sv (SLit 0)) = m.
Proof.
  intros E m HM. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, HM, (zcanon_id 0) by (unfold M64; lia).
  rewrite Z.add_0_r. apply zcanon_id. pose proof (U_range E h_magic_sv) as HR. rewrite HM in HR. exact HR.
Qed.


Section magic.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg pcap_listing}.
#[local] Notation VAL := (@pa_val _ pcap_listing PI).

Definition h_magic_X (cx : ecx) : Z := if nth 3 (p_C cx) 0 <? 128 then 0 else 2 ^ 64 - 2 ^ 32.

Lemma h_magic_bytes : forall cx, PST.pcap_magic (p_F cx) =
  nth 0 (p_C cx) 0 + 256 * nth 1 (p_C cx) 0 + 65536 * nth 2 (p_C cx) 0 + 16777216 * nth 3 (p_C cx) 0.
Proof. intros cx. unfold PST.pcap_magic, p_C. rewrite !h_bt. reflexivity. Qed.

Lemma h_magic_U_cx : forall E cx,
  ew E 34 = Z_to_bv 64 (nth 0 (p_C cx) 0) -> ew E 35 = Z_to_bv 64 (nth 1 (p_C cx) 0) ->
  ew E 36 = Z_to_bv 64 (nth 2 (p_C cx) 0) -> ew E 37 = Z_to_bv 64 (nth 3 (p_C cx) 0) ->
  U E h_magic_sv = PST.pcap_magic (p_F cx) + h_magic_X cx.
Proof.
  intros E cx E0 E1 E2 E3.
  rewrite (h_magic_U E _ _ _ _ E0 E1 E2 E3) by apply h_bt_range.
  rewrite h_magic_bytes. unfold h_magic_X. lia.
Qed.

(* U = the 32-bit sign-extended literal exactly for the model's magic. *)
Lemma h_U_K : forall cx,
  (PST.pcap_magic (p_F cx) + h_magic_X cx = h_K1 <-> PST.pcap_magic (p_F cx) = 2712847316) /\
  (PST.pcap_magic (p_F cx) + h_magic_X cx = h_K2 <-> PST.pcap_magic (p_F cx) = 3569595041).
Proof.
  intros cx. pose proof (h_magic_bytes cx) as HB.
  pose proof (h_bt_range (p_F cx) 0) as R0. pose proof (h_bt_range (p_F cx) 1) as R1.
  pose proof (h_bt_range (p_F cx) 2) as R2. pose proof (h_bt_range (p_F cx) 3) as R3.
  fold (p_C cx) in R0, R1, R2, R3. unfold h_magic_X, h_K1, h_K2.
  destruct (Z.ltb_spec (nth 3 (p_C cx) 0) 128); split; split; lia.
Qed.

Lemma h_good_cases : forall cx, p_good cx = true ->
  24 <= p_nF cx /\
  ((PST.pcap_magic (p_F cx) = 2712847316 /\ p_swz cx = 0) \/ (PST.pcap_magic (p_F cx) = 3569595041 /\ p_swz cx = 1)).
Proof.
  intros cx HG. unfold p_good, PST.pcap_good in HG. apply andb_prop in HG as [H24 HM].
  apply Z.leb_le in H24. unfold p_nF. split; [exact H24|].
  unfold p_swz, PST.pcap_sw. apply orb_prop in HM as [HM | HM]; apply Z.eqb_eq in HM; rewrite HM.
  - left. split; reflexivity.
  - right. split; reflexivity.
Qed.

Lemma h_bad_magic : forall cx, p_good cx = false -> 24 <= p_nF cx ->
  PST.pcap_magic (p_F cx) <> 2712847316 /\ PST.pcap_magic (p_F cx) <> 3569595041.
Proof.
  intros cx HG H24. unfold p_good, PST.pcap_good in HG.
  apply andb_false_iff in HG as [HG | HG].
  - apply Z.leb_gt in HG. unfold p_nF in H24. lia.
  - apply orb_false_iff in HG as [H1 H2]. apply Z.eqb_neq in H1. apply Z.eqb_neq in H2. split; assumption.
Qed.
End magic.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is EXPLICIT on every lemma of this file (a Theorem Labs lane, 21:57Z): the only global sink_head instance in this
   closure is the plain build's, so it must never be inferred. *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head).
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis NEXT : tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NX_STK B MT KS (BASE + AF_pcap_source_next).
(* RO is an EXPLICIT Section hypothesis (was a maximal implicit {RO}, which a caller without @ would fill by instance
   search: the risky shape the sink-head incident showed; a Theorem Labs lane's PcapEntryFinal finding, 06:16Z). *)
Hypothesis RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.

(* ---- what pe_base gives the walks of this file, by name ---- *)
Lemma h_base : forall cx, pe_base SK B MT KS cx ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
  asrc_meta_inv SEGS KS (c_ly cx) (rdW (c_W cx) (c_mem cx)) (c_M cx) /\
  gx_ok SEGS B pe_G /\
  (forall a, inG pe_G a -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a /\
     ~ (as_meta_mem KS <= a < as_meta_mem KS + 8) /\ ~ (as_errno B <= a < as_errno B + 4) /\
     ~ (AOFL_HEAD <= a < AOFL_HEAD + 8) /\ ~ asrc_env_addr KS a /\ (forall m, writable_at SEGS m a)).
Proof.
  intros cx (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _ & _ & HME & _ & _ & _ & _ & _ & HG & HGR & _).
  split; [exact HRO|]. split; [exact HME|]. split; [exact HG | exact HGR].
Qed.

(* g_file_len (object 4) lies wholly below g_file (object 2) (pe_base's object-separation conjunct). *)
Lemma h_base_objsep : forall cx, pe_base SK B MT KS cx -> VAL (A_OBJ 4) + 8 <= VAL (A_OBJ 2).
Proof.
  intros cx (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSEP & _). exact HSEP.
Qed.

(* A byte at or above the low memory's end is no byte of the harness's globals. *)
Lemma h_notG_hi : forall a, gx_ok SEGS B pe_G -> kLowMemEnd <= a < 2 ^ 64 ->
  inGb pe_G (bv_unsigned (Z_to_bv 64 a)) = false.
Proof.
  intros a HG Ha. rewrite unsigned_lit_small by (unfold kLowMemEnd in Ha; lia). apply inGb_false. intros Hin.
  destruct (HG a Hin) as [Himg _]. pose proof (pa_segs_low a Himg). lia.
Qed.

Lemma h_notG : forall a, 0 <= a < 2 ^ 64 -> ~ inG pe_G a -> inGb pe_G (bv_unsigned (Z_to_bv 64 a)) = false.
Proof. intros a Ha Hn. rewrite unsigned_lit_small by lia. apply inGb_false. exact Hn. Qed.

Lemma h_img_range : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64.
Proof. intros a Ha. pose proof (pa_segs_low a Ha). unfold kLowMemEnd in *. lia. Qed.

Lemma h_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Ha) | Ha]; [exists s; split; [exact Hs | exact Ha] | exact (pa_relro_img a Ha)].
Qed.

(* The read-only data at the gx journal's inner start memory. *)
Lemma h_arodata_S : forall cx memS, pe_base SK B MT KS cx -> gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) memS).
Proof.
  intros cx memS HB HAG a Hro Hno Her. destruct (h_base cx HB) as (HRO & _ & _ & HGR).
  rewrite (aview_gagree SEGS pe_G _ _ _ a HAG).
  - exact (HRO a Hro Hno Her).
  - apply h_notG; [exact (h_img_range a (h_roP_img a Hro))|]. intros Hin. exact (proj1 (HGR a Hin) Hro).
Qed.

(* The meta region at the end of a gx journal (PSourceMeta.asrc_meta_inv_kept, from the caller's memory through the
   journal's start memory memS). *)
Lemma h_meta_gx : forall cx memS own ly' S' W' mem' md' k, pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly' S' W' mem' md' k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  asrc_meta_inv SEGS KS ly' (rdW W' mem') (c_M cx).
Proof.
  intros cx memS own ly' S' W' mem' md' k HB HJ HAG.
  destruct (h_base cx HB) as (_ & (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ) & HG & HGR).
  pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  assert (HX' : In (c_M cx, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
  split; [exact HX'|]. split; [exact Himg|]. split; [exact (asrc_meta_ptr_of_AR SK SEGS B KS ASIL _ _ _ _ _ HAR')|]. split.
  - eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply mbyte_kept_of_aview.
    destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
    rewrite (F3 x Hi Hns He) by (apply fp_spares_below; exact Hlt).
    apply (aview_gagree SEGS pe_G _ _ _ x HAG). apply h_notG; [exact (h_img_range x Hi)|].
    intros Hin. apply (proj1 (proj2 (HGR x Hin))). lia.
  - split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
    intros a Ha. rewrite <- (HZ a Ha). apply mbyte_kept_of_aview.
    rewrite F5.
    + apply (aview_gagree SEGS pe_G _ _ _ a HAG). apply h_notG; [unfold AMETA_SIZE in *; lia|].
      intros Hin. destruct (HG a Hin) as [Hi _]. pose proof (Himg a Hi). lia.
    + apply Exists_exists. exists (c_M cx, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
    + intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi.
      destruct (AR_extra_law_ok SEGS B ly' S' W' mem' md' a HAR'
        ltac:(apply Exists_exists; exists (c_M cx, AMETA_SIZE); split; [exact HX' | unfold in_zr; cbn [fst snd]; lia]))
        as (_ & _ & _ & _ & Hni & _).
      exact (Hni Hi).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Memory and value helpers                                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma h_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma h_denot_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
  intros E n v x F Hv. rewrite denot_lit_U, U_SOff, F, unsigned_lit_small by exact Hv.
  unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Lemma h_w64_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Lemma hsh_chunks_ok : forall (E : env) H (m : word -> option byte) base sh i,
  (forall j, (j < length sh)%nat -> aview SEGS H m (base + (i + Z.of_nat j)) = Some (nth j sh 0)) ->
  Forall (YP09.chunk_ok SEGS E (mrestrict H m) base) (hsh_chunks i sh).
Proof.
  intros E H m base sh. induction sh as [|v t IH]; intros i Hv; cbn [hsh_chunks]; [constructor|].
  constructor.
  - pose proof (Hv 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0. rewrite Z.add_0_r in H0.
    destruct (val_mem1_of_aview SEGS H m (base + i) v H0) as [Hm Hb].
    apply (chunk_ok_val SEGS E (mrestrict H m) base i 1%N (SLit v) v); [reflexivity | cbn; lia | cbn; lia | exact Hm].
  - apply IH. intros j Hj. pose proof (Hv (S j) ltac:(cbn [length]; lia)) as Hs. cbn [nth] in Hs.
    replace (base + (i + 1 + Z.of_nat j)) with (base + (i + Z.of_nat (S j))) by lia. exact Hs.
Qed.

Lemma h_slot_chunk_ok : forall (E : env) H (m : word -> option byte) base off e v,
  rdword (aview SEGS H m) (base + off) = Some v -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E H m base off e v Hr He Hv.
  apply (chunk_ok_val SEGS E (mrestrict H m) base off 8%N e v); [exact He | cbn; lia | cbn; lia|].
  apply (val_mem_of_rdword SEGS H m). exact Hr.
Qed.

Lemma h_rdword_keep : forall H H' (m m' : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> aview SEGS H' m' (a + i) = aview SEGS H m (a + i)) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H' m') a = Some v.
Proof.
  intros H H' m m' a v K Hr. unfold rdword in Hr |- *.
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (K 1 ltac:(lia)), (K 2 ltac:(lia)), (K 3 ltac:(lia)), (K 4 ltac:(lia)), (K 5 ltac:(lia)),
    (K 6 ltac:(lia)), (K 7 ltac:(lia)). exact Hr.
Qed.

(* A value's bytes as a field of a region of the symbolic state. *)
Lemma h_field : forall E ss ms i n lo hi wlo whi cs b od (w : N) e v,
  st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (ms_mem ms) (b + od) (N.to_nat w) v.
Proof.
  intros E ss ms i n lo hi wlo whi cs b od w e v HS Hi Hb Hin He Hv Hw.
  exact (field_of_region E (ms_mem ms) n b cs lo hi wlo whi od w e v (st_ok_region_nth E ss ms i _ HS Hi) Hb Hin He Hv Hw).
Qed.

Lemma h_div8_of_mul64 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
  intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
  symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.

(* The machine state of a cut, as the state the engine starts from. *)
Lemma h_restrict_body : forall cx fp pc W3 ms3 sh, pe_body cx fp pc W3 ms3 sh ->
  restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (rdW W3 (ms_mem ms3)) (seg_rom SEGS).
Proof.
  intros cx fp pc W3 ms3 sh (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & _).
  destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts of the start and of the frame                                                              *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma h_sp : forall cx, pe_base SK B MT KS cx ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 256 < c_sp1 cx <= spZ (c_regs cx) - 224 /\ c_sp1 cx mod 32 = 0.
Proof.
  intros cx HB.
  destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & _).
  unfold LLVMF_STK in *. rewrite Hsp1. unfold pe_sp1, PE_MFRAME.
  pose proof (Z.div_mod (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hmp.
  split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Lemma h_frame : forall cx fp m0 ly3 S3 W3 mem md3 k, pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) m0 (c_md cx)
    [(PE_CID, fp)] ly3 S3 W3 mem md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  frame_addr ly3 PE_CID fp = pF cx fp /\ flag_addr ly3 PE_CID fp = pFL cx fp /\
  4096 <= pF cx fp /\ pF cx fp + 128 <= alloc_ceiling /\ pF cx fp mod 64 = 0 /\
  in_app (pF cx fp) 128 /\ off_img (pF cx fp) 128 /\ pSH cx fp = SHADOW_OFF + pF cx fp / 8 /\
  (forall a, pF cx fp <= a < pF cx fp + 128 -> apresent (w_H W3) mem a) /\
  (forall i, 0 <= i < 16 -> apresent (w_H W3) mem (pSH cx fp + i)).
Proof.
  intros cx fp m0 ly3 S3 W3 mem md3 k HB HJ HFR.
  pose proof HJ as (HAR3 & Hly3 & _).
  destruct HB as ((HAR0 & _) & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (EF : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF; apply Efa).
  assert (EFL : flag_addr ly3 PE_CID fp = pFL cx fp).
  { pose proof (Efa 0 0) as E00. unfold frame_addr in E00. unfold pFL, flag_addr. lia. }
  assert (Hfb : fs_frame_bytes PE_CID = 128) by (vm_compute; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR3 Hfin) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 mem md3 PE_CID fp HAR3 Hfin) as HFo.
  destruct (frame_al64 SEGS B ly3 S3 W3 mem md3 PE_CID fp HAR3 Hfin) as (Hal & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR3 Hfin) as (_ & _ & HFpres & HFSpres).
  rewrite EF, Hfb in *.
  split; [reflexivity|]. split; [exact EFL|]. split; [exact HF0|]. split; [exact HFc|]. split; [exact Hal|].
  split; [exact HFia|]. split; [exact HFo|]. split; [unfold pSH, shadow_of_addr; reflexivity|].
  split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
  intros i Hi. change (128 / 8) with 16 in HFSpres.
  replace (pSH cx fp) with (shadow_addr (pF cx fp)) by (unfold pSH, shadow_of_addr, shadow_addr; reflexivity).
  exact (proj1 (HFSpres i Hi)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Walk C: PP_K3 (0x80abc) -> pcap_source_next (0x80af0) -> PP_KD (0x80af4)                        *)
(* ---------------------------------------------------------------------------------------------- *)
(* 0x80abc beqz a0 to the abort (closed: buf >= 4096 is an atom fact the engine decides); 0x80ac0 s6 := buf;
   0x80ac4 / 0x80ac8 / 0x80ad0 the slots 24, 16, 8 := s4 = F, s7 = F, s9 = SH; 0x80acc a3 := F + 96; 0x80ad4 shadow
   byte 12 := 0 (ts in scope); 0x80adc ts := -1; 0x80ae0 a0 := ps (slot 88); a1 := buf; a2 := cap; 0x80aec slot
   80 := F + 96; 0x80af0 jal pcap_source_next. The symbolic state: the slots s1 + [0, 96) (with d at 32, the
   auipc value of g_file_len at 64, ps at 88), the frame's 16 shadow bytes at s9 (byte 12 writable) and ts at
   s7 + 96. *)
Definition hR_slotsC : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 96 0 96
    [YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff (A_HI 8) 0)); YP09.mkChunk 88 (CVal 8 (SOff 23 32))].
Definition hR_shC : YP09.region := YP09.mkRegion (Some 25%nat) 0 16 12 13 (hsh_chunks 0 PSH_ps).
Definition hR_tsC : YP09.region := YP09.mkRegion (Some 23%nat) 96 104 96 104 [].
Definition hfacts_C : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 4);
           (23%nat, mkAF 4096 (2 ^ 47) 6); (25%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3)] [] [].
Definition hss_C : sstate := mkSS PP_K3 sr_atoms [hR_slotsC; hR_shC; hR_tsC] None hfacts_C.
Definition hBspan0 : Z * Z := (0, 0).

(* ---- the blocks the call holds: no two are the same, and the ones it allocated are fresh ---- *)
Lemma h_nodup_app_disj : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 x Hnd Hx Hin; [destruct Hin|].
  inversion Hnd as [|a' l' Hna Hnd']; subst.
  destruct Hin as [<-|Hin]; [apply Hna; apply in_or_app; right; exact Hx | exact (IH l2 x Hnd' Hx Hin)].
Qed.

Lemma h_nodup_blocks : forall L : list (Z * Z),
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) L) -> Forall (fun b => 0 <= snd b) L -> List.NoDup L.
Proof.
  induction L as [|x L IH]; intros Hp Hn; [constructor|].
  cbn [map pairwise] in Hp. destruct Hp as [Hx Hp]. inversion Hn as [|x' L' Hx0 Hn']; subst.
  constructor; [|exact (IH Hp Hn')].
  intros Hin. rewrite Forall_forall in Hx.
  specialize (Hx (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) L x Hin)).
  pose proof (req_size_pos (snd x) Hx0) as [Hr _]. unfold zdisjoint in Hx. cbn [fst snd] in Hx. lia.
Qed.

Lemma h_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. destruct (ablocks B ly S) as [|[p n] l] eqn:EL; [constructor|].
  assert (Hin : In (p, n) (ablocks B ly S)) by (rewrite EL; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite <- EL. apply h_nodup_blocks; [exact Hpw|].
  apply Forall_forall. intros [q m] Hq. destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hq) as (_ & _ & _ & _ & _ & _ & Hm).
  cbn [snd]. lia.
Qed.

(* Three blocks the call allocated, on top of the caller's: each is a block, each is fresh, and they are
   pairwise apart. *)
Lemma h_blocks3 : forall ly S (W : world SEGS) mem md L0 x y z,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (L0 ++ [x; y; z]) ->
  In x (ablocks B ly S) /\ In y (ablocks B ly S) /\ In z (ablocks B ly S) /\
  ~ In x L0 /\ ~ In y L0 /\ ~ In z L0 /\
  zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y)) /\
  zdisjoint (fst x, req_size (snd x)) (fst z, req_size (snd z)) /\
  zdisjoint (fst y, req_size (snd y)) (fst z, req_size (snd z)).
Proof.
  intros ly S W mem md L0 x y z HAR HP.
  pose proof (Permutation_NoDup HP (h_ablocks_nodup ly S W mem md HAR)) as Hnd.
  assert (HinL : forall q, In q [x; y; z] -> In q (ablocks B ly S))
    by (intros q Hq; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hq).
  pose proof (NoDup_app_remove_l _ _ Hnd) as Hnd3.
  inversion Hnd3 as [|x' l' Hx3 Hnd2]; subst. inversion Hnd2 as [|y' l'' Hy2 Hnd1]; subst.
  assert (Hxy : x <> y) by (intros ->; apply Hx3; left; reflexivity).
  assert (Hxz : x <> z) by (intros ->; apply Hx3; right; left; reflexivity).
  assert (Hyz : y <> z) by (intros ->; apply Hy2; left; reflexivity).
  destruct x as [px nx], y as [py ny], z as [pz nz].
  pose proof (HinL _ (or_introl eq_refl)) as Hx. pose proof (HinL _ (or_intror (or_introl eq_refl))) as Hy.
  pose proof (HinL _ (or_intror (or_intror (or_introl eq_refl)))) as Hz.
  split; [exact Hx|]. split; [exact Hy|]. split; [exact Hz|].
  split; [exact (h_nodup_app_disj _ L0 _ _ Hnd (or_introl eq_refl))|].
  split; [exact (h_nodup_app_disj _ L0 _ _ Hnd (or_intror (or_introl eq_refl)))|].
  split; [exact (h_nodup_app_disj _ L0 _ _ Hnd (or_intror (or_intror (or_introl eq_refl))))|].
  split; [exact (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hx Hy Hxy)|].
  split; [exact (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hx Hz Hxz)|].
  exact (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hy Hz Hyz).
Qed.

(* ---- the call chain the body hands to its callees (cgif lib/A/ACf5.v:172 rt_chain; a Theorem Labs lane's ge_achain) ---- *)
Lemma h_achain : forall cx memS ly3 S3 W3 mem md own k sp', pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem md k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain ly3 (aview SEGS (w_H W3) mem) sp' (spZ (c_regs cx)) (pch cx).
Proof.
  intros cx memS ly3 S3 W3 mem md own k sp' HB HJ HAG H8 H16 Hsp.
  destruct (h_base cx HB) as (_ & _ & HG & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof asan_consts as (C1 & _).
  apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
  assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
  unfold pch. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
  - apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) mem)
             (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] sp' Hch).
    + lia.
    + intros a Ha. etransitivity; [apply F1; unfold LLVMF_STK; lia|].
      apply (aview_gagree SEGS pe_G _ _ _ a HAG). apply h_notG_hi; [exact HG|]. unfold kLowMemEnd. lia.
    + exact H8.
    + exact H16.
    + exact Hra4.
    + lia.
    + exact Hal8.
    + lia.
    + exact Hsp.
  - left. split; [right; left; lia | reflexivity].
Qed.

(* ---- the shadow of a range of the frame, from its shadow bytes ---- *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma h_ra_frame : forall H (m : word -> option byte) F SH lo n,
  SH = SHADOW_OFF + F / 8 -> F mod 64 = 0 -> 0 <= lo -> lo mod 8 = 0 -> 0 <= n ->
  (forall j, 0 <= j < (n + 7) / 8 -> aview SEGS H m (SH + lo / 8 + j) = Some 0) ->
  range_addressable (aview SEGS H m) SHADOW_OFF (F + lo) n.
Proof.
  intros H m F SH lo n Hdef HF Hlo0 Hlo8 Hn HZ x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  assert (Hq : x / 8 = F / 8 + lo / 8 + (x - (F + lo)) / 8) by lia.
  rewrite Hq. replace (SHADOW_OFF + (F / 8 + lo / 8 + (x - (F + lo)) / 8)) with (SH + lo / 8 + (x - (F + lo)) / 8) by lia.
  apply HZ. lia.
Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma h_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. specialize (HP (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in HP. exact HP. Qed.

Lemma h_mod32_8 : forall z, z mod 32 = 0 -> z mod 16 = 0 /\ z mod 8 = 0.
Proof.
  intros z H. apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. subst z.
  split; [replace (q * 32) with ((2 * q) * 16) by lia | replace (q * 32) with ((4 * q) * 8) by lia]; apply Z_mod_mult.
Qed.

Lemma h_mod64_add : forall z c, z mod 64 = 0 -> c mod 8 = 0 -> (z + c) mod 8 = 0.
Proof.
  intros z c Hz Hc. apply Z.mod_divide in Hz; [|lia]. apply Z.mod_divide in Hc; [|lia].
  destruct Hz as [q Hq]. destruct Hc as [r Hr]. subst. replace (q * 64 + r * 8) with ((8 * q + r) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma h_apresent_mbyte : forall H (m : word -> option byte) a, apresent H m a -> exists b, mbyte SEGS (mrestrict H m) a = Some b.
Proof. intros H m a [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. Qed.

Lemma PSH_ts_range : forall i, 0 <= nth i PSH_ts 0 < 256.
Proof. intros i. do 16 (destruct i as [|i]; [cbn; lia|]). destruct i; cbn; lia. Qed.

Lemma h_nx_model : forall cx p,
  nx_q (p_swz cx =? 1) (p_C cx) (p_cap cx) p = p_q cx p /\
  nx_lh (p_swz cx =? 1) (p_C cx) (p_cap cx) p = PSN.psn_lh (p_sw cx) (p_F cx) (p_cap cx) p /\
  nx_res (p_swz cx =? 1) (p_C cx) (p_cap cx) p = p_res cx (p_q cx p) /\
  nx_pos (p_swz cx =? 1) (p_C cx) (p_cap cx) p = p_pos cx (p_q cx p) /\
  nx_kind (p_swz cx =? 1) (p_C cx) (p_cap cx) p = p_kind cx (p_q cx p) /\
  nxF (p_C cx) = p_F cx.
Proof.
  intros cx p. unfold nx_res, nx_pos, nx_kind, nx_lh, nx_q, nxF, p_q, p_res, p_pos, p_kind, p_sw, p_C.
  rewrite h_bytesZ_unsigned. repeat split; reflexivity.
Qed.


(* A run whose regions all have empty write windows changed no byte. *)
Lemma h_kept_nowin : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  Forall (fun w : option nat * Z * Z => snd (fst w) = snd w) (windows rs) ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' HF HW a Ha.
  apply (kept_of_frame (segs := SEGS) E rs H m m' (fun _ : Z => False) HF); [|exact Ha | intros []].
  intros bb wlo whi x Hin Hx. rewrite Forall_forall in HW. specialize (HW _ Hin). cbn in HW. lia.
Qed.

(* lia over the one or two disjunctive separation facts a goal needs, kept folded in the context (zdisjoint, in_app,
   off_img) so that the other calls do not case-split on all of them. *)
Ltac acs := unfold acallee_saved; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
  | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
  | right; right; right; right; right; split; vm_compute; discriminate].
(* every region of walk B has an empty write window, so no run of the walk writes *)
Ltac hawr0 := apply awr_ok_x_of0; intros aa (rr & Hin & Hr); exfalso; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia |]);
  destruct Hin.
(* a0 = -1 at walk B's refused arm, as the engine's environment sees it *)
Ltac hx10 Ex R10 EE X10 :=
  assert (X10 : ew Ex 10 = Z_to_bv 64 18446744073709551615)
    by (rewrite ?ew_ewset_other by lia; rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; apply bv_eq;
        rewrite !Z_to_bv_unsigned; reflexivity).
Ltac hkr HFr Hprev :=
  let aa := fresh "a" in let Haa := fresh "Ha" in
  intros aa Haa; etransitivity;
  [ refine (h_kept_nowin _ _ _ _ _ HFr ltac:(clear; vm_compute; repeat constructor) aa Haa)
  | exact (Hprev aa Haa) ].
Ltac zuf H := unfold zdisjoint, in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in H;
  cbn [fst snd] in H.
Ltac dlia1 H := let X := fresh "X" in pose proof H as X; zuf X; lia.
Ltac dlia2 H1 H2 := let X := fresh "X" in pose proof H1 as X; zuf X; dlia1 H2.
Ltac dlia3 H1 H2 H3 := let X := fresh "X" in pose proof H1 as X; zuf X; dlia2 H2 H3.



(* ---- walk C, the call of pcap_source_next (0x80af0) and the return to PP_KD (0x80af4) ---- *)
(* The state at the call, as the run of walk C leaves it (pe_C below): the registers, the bytes the run wrote (the
   slots s1 + [0, 96), shadow byte 12, ts) and everything else as at PP_K3. *)
Lemma h_C_next : forall POST, pe_from SK B MT KS POST (GI_KD B MT KS) ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf (regs : bvmap 5 word) mem mdc,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  p_cut B cx fp PP_K3 PSH_ps k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 ->
  c_n cx < 2 ^ 26 -> p_good cx = true ->
  getr (ms_regs ms3) 20 = w64 (pF cx fp) ->
  p_glob cx W3 ms3 b -> p_psopen cx fp W3 ms3 h -> p_psfresh cx fp W3 ms3 ->
  asource_at SEGS KS (rdW W3 (ms_mem ms3)) h b (p_C cx) 24 ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem mdc k ->
  m_fds mdc = m_fds md3 -> m_fs mdc = m_fs md3 ->
  getr regs 1 = Z_to_bv 64 (BASE + 956) -> getr regs 2 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
  getr regs 10 = Z_to_bv 64 (pF cx fp + 32) -> getr regs 11 = w64 buf -> getr regs 12 = w64 (p_cap cx) ->
  getr regs 13 = Z_to_bv 64 (pF cx fp + 96) -> getr regs 19 = w64 b -> getr regs 21 = w64 (p_cap cx) ->
  getr regs 22 = w64 buf -> getr regs 27 = w64 SHADOW_OFF ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((c_sp1 cx <= a < c_sp1 cx + 96) \/ (pSH cx fp + 12 <= a < pSH cx fp + 13) \/ (pF cx fp + 96 <= a < pF cx fp + 104)) ->
     aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 88) = Some (pF cx fp + 32) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 64) = Some (VAL (A_HI 8)) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 32) = Some (p_d cx) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 8) = Some (pSH cx fp) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 16) = Some (pF cx fp) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 24) = Some (pF cx fp) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 80) = Some (pF cx fp + 96) ->
  (forall i, (i < 16)%nat -> aview SEGS (w_H W3) mem (pSH cx fp + Z.of_nat i) = Some (nth i PSH_ts 0)) ->
  val_mem SEGS (rdW W3 mem) (pF cx fp + 96) 8 18446744073709551615 ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_pcap_source_next)) mem (seg_rom SEGS)) mdc) (POST cx).
Proof.
  intros POST HKD cx fp k acc ly3 S3 W3 ms3 md3 b h buf regs mem mdc HB HJ HFR HMO HCUT Hn26 Hgood R20 HGL HPSO HPSF HSRC
    HJc Hfdsc Hfsc Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q13 Q19 Q21 Q22 Q27 KR SLpsp SLglen SLd SLsh SLf SLfk SLts SHm TSm.
  destruct HCUT as (HBODY & Hk & Hacc & HPERM & Hfds & Hfs).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G27 & G3 & G4) & HSAVED & HHDR & HSH &
                       Hlen & HIN).
  pose proof (h_sp cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  destruct (h_base cx HB) as (HROD & HMETA & HG & HGR).
  pose proof HJ as HJgx. destruct HJ as (_ & _ & (memS & HJ & HAG) & _). rewrite !Z.add_0_r in HJ.
  pose proof (h_frame cx fp memS ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR)
    as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof (p_d_range cx) as Hd.
  pose proof (h_blocks3 ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ HAR3 HPERM)
    as (Hb_in & Hh_in & Hbuf_in & Hb_fr & Hh_fr & Hbuf_fr & Dbh & Dbbuf & Dhbuf).
  cbn [fst snd] in Dbh, Dbbuf, Dhbuf.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hh_in) as (_ & Hh4096 & Hhceil & Hhapp & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbuf_in) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _ & _ & _).
  pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hreqbn].
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil, Dbh, Dhbuf.
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hbuf_in Hfin) as Dbuf.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hh_in Hfin) as Dh.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hb_in Hfin) as Db.
  rewrite EF in Dbuf, Dh, Db. change (fs_frame_bytes PE_CID) with 128 in Dbuf, Dh, Db.
  change (req_size SRC_FILE_BLOCK) with 1304 in Dh, Hhapp.
  assert (HSHr : SB + 512 <= pSH cx fp /\ pSH cx fp + 16 <= SB + 2 ^ 44 /\ pSH cx fp mod 8 = 0).
  { destruct (h_div8_of_mul64 (pF cx fp) HF64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF, SB.
    pose proof (Z.div_lt_upper_bound (pF cx fp + 128) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_lower_bound (pF cx fp) 8 512 ltac:(lia) ltac:(lia)).
    replace ((pF cx fp + 128) / 8) with (pF cx fp / 8 + 16) in H
      by (rewrite <- (Z.div_add (pF cx fp) 16 8) by lia; f_equal; lia).
    split; [lia|]. split; [lia|].
    rewrite E8. replace (2147450880 + 8 * (pF cx fp / 64)) with ((268431360 + pF cx fp / 64) * 8) by lia.
    apply Z_mod_mult. }
  unfold SB in HSHr.
  (* the frame lies in application memory, its shadow in the shadow band *)
  assert (DFSH : pF cx fp + 128 <= pSH cx fp \/ pSH cx fp + 16 <= pF cx fp).
  { clear - HFapp HSHr C1 C3. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
  destruct HJc as (_ & _ & (memS' & HJm & HAGm) & _). rewrite !Z.add_0_r in HJm.
  pose proof HJm as (HARm & _).
  assert (Esp : spZ regs = c_sp1 cx) by (unfold spZ; rewrite Q2; apply h_w64_unsigned; lia).
  assert (Es0 : s0Z regs = spZ (c_regs cx)) by (unfold s0Z; rewrite Q8; apply h_w64_unsigned; lia).
  assert (MK : forall a, 0 <= a < 2 ^ 64 ->
     ~ ((c_sp1 cx <= a < c_sp1 cx + 96) \/ (pSH cx fp + 12 <= a < pSH cx fp + 13) \/ (pF cx fp + 96 <= a < pF cx fp + 104)) ->
     mbyte SEGS (rdW W3 mem) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a)
    by (intros a Ha Hn; apply (mbyte_of_aview SEGS); exact (KR a Ha Hn)).
  (* the record buffer's bytes, as the next call's premise names them *)
  destruct (garr8_of_readable SEGS (rdW W3 mem) buf (Z.to_nat (p_bn cx))) as (bj & Hbjlen & Hbj).
  { intros a Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARm Hbuf_in) as (_ & _ & _ & _ & Hpm & _).
    apply h_apresent_mbyte. apply (proj1 (Hpm a ltac:(lia))). }
  pose proof HB as ((_ & _ & Hra4 & Hgp0 & Htp0 & _) & _ & _ & _ & HINP & _).
  destruct HPSO as (HPSO1 & HPSO2). destruct HPSF as (HPF12 & HPF16 & HPF20 & HPF22).
  unfold p_pspad, pval, pPS, PO_PS in HPSO1, HPSO2, HPF12, HPF16, HPF20, HPF22.
  assert (PSm : forall o n v, 0 <= o -> o + Z.of_nat n <= 24 ->
     val_mem SEGS (rdW W3 (ms_mem ms3)) (pF cx fp + 32 + o) n v -> val_mem SEGS (rdW W3 mem) (pF cx fp + 32 + o) n v).
  { intros o n v Ho1 Ho2 Hv. eapply vm_frame; [|exact Hv]. intros x Hx. apply MK; lia. }
  assert (HLC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
  assert (HL24 : 24 <= p_nF cx).
  { unfold p_good, PST.pcap_good in Hgood. apply andb_prop in Hgood as [H24 _]. apply Z.leb_le in H24. exact H24. }
  eapply SRr_bind.
  { eapply (NEXT LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS' (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 mem mdc k regs
      (pF cx fp + 32) buf (p_cap cx) (pF cx fp + 96) h b 24 (p_swz cx) 0 0 0 18446744073709551615 (c_M cx) PE_CID fp
      (p_C cx) bj [165; 165] (pch cx)).
    - exact HJm.
    - eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJm | exact (h_arodata_S cx memS' HB HAGm)].
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite Q1, unsigned_lit_small; pose proof pa_base_lo; pose proof pa_B_ok; lia.
    - rewrite Q3. exact Hgp0.
    - rewrite Q4. exact Htp0.
    - rewrite Q10. reflexivity.
    - exact Q11.
    - exact Q12.
    - rewrite Q13. reflexivity.
    - rewrite Esp. exact (proj1 (h_mod32_8 _ Hsp1_32)).
    - rewrite Esp. unfold LLVMF_STK, NX_STK, AFREAD_STK. lia.
    - rewrite Esp. lia.
    - rewrite Esp, Es0. apply (h_achain cx memS' ly3 S3 W3 mem _ [(PE_CID, fp)] k (c_sp1 cx) HB HJm HAGm).
      + apply (h_rdword_keep (w_H W3) (w_H W3) (ms_mem ms3) mem); [|exact (proj1 HSAVED)].
        intros i Hi. apply KR; lia.
      + pose proof (proj2 HSAVED 0 ltac:(lia)) as HS0. rewrite Z.mul_0_r, Z.sub_0_r in HS0.
        apply (h_rdword_keep (w_H W3) (w_H W3) (ms_mem ms3) mem); [|exact HS0].
        intros i Hi. apply KR; lia.
      + lia.
    - rewrite HFR. vm_compute. reflexivity.
    - unfold PS_F_OFF. rewrite Z.add_0_r. rewrite <- (Z.add_0_r (pF cx fp + 32)). apply (PSm 0 8%nat); [lia | cbn; lia |].
      rewrite Z.add_0_r. exact HPSO1.
    - lia.
    - apply h_mod64_add; [exact HF64 | reflexivity].
    - lia.
    - unfold PS_LEN. lia.
    - unfold amem_range, PS_LEN. dlia1 HFapp.
    - left. reflexivity.
    - rewrite EF. lia.
    - rewrite EF. change (fs_frame_bytes PE_CID) with 128. unfold PS_LEN. lia.
    - unfold PS_LEN. apply (h_ra_frame (w_H W3) mem (pF cx fp) (pSH cx fp) 32 24 ESH HF64); [lia | reflexivity | lia |].
      intros j Hj. change ((24 + 7) / 8) with 3 in Hj. change (32 / 8) with 4.
      replace (pSH cx fp + 4 + j) with (pSH cx fp + Z.of_nat (Z.to_nat (4 + j))) by lia.
      rewrite SHm by lia. assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia.
      destruct Hj3 as [-> | [-> | ->]]; reflexivity.
    - intros _. unfold nx_ps_at, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF.
      split; [apply (PSm 0 8%nat); [lia | cbn; lia | rewrite Z.add_0_r; exact HPSO1]|].
      split; [apply (PSm 8 4%nat); [lia | cbn; lia | exact HPSO2]|].
      split; [apply (PSm 12 4%nat); [lia | cbn; lia | exact HPF12]|].
      split; [apply (PSm 16 4%nat); [lia | cbn; lia | exact HPF16]|].
      split; [apply (PSm 20 2%nat); [lia | cbn; lia | exact HPF20]|].
      split; [|reflexivity].
      apply (garr8_frame SEGS (rdW W3 (ms_mem ms3)) (rdW W3 mem) _ _ HPF22).
      intros x Hx. cbn [length] in Hx. apply MK; lia.
    - intros _. unfold p_swz, PST.pcap_sw. destruct (_ =? _); [right | left]; reflexivity.
    - intros _. lia.
    - intros _ a Ha. unfold PS_LEN in Ha. rewrite Esp. split; [|unfold NX_STK, AFREAD_STK; lia].
      right; right; right. exists PE_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [frame_rng fst snd].
      rewrite EF. change (fs_frame_bytes PE_CID) with 128. lia.
    - intros _. unfold nx_bufn, NX_CAP_MAX. fold (p_bn cx). rewrite Esp.
      split; [exact Hbuf_in|]. split; [lia|]. split; [lia|]. split; [exact Hbj|]. split; [lia|]. split; [lia|].
      split; [|unfold PS_LEN; dlia1 Dbuf].
      intros a Ha. split; [|unfold NX_STK, AFREAD_STK; lia].
      right; right; left. exists buf, (p_bn cx). split; [exact Hbuf_in|]. split; [exact Hbuf_fr | lia].
    - intros _ _. rewrite Esp. split; [exact TSm|]. split; [apply h_mod64_add; [exact HF64 | reflexivity]|].
      split; [lia|]. split; [lia|]. split; [unfold amem_range; dlia1 HFapp|].
      split; [exists PE_CID, fp; split; [left; reflexivity|]; rewrite EF; change (fs_frame_bytes PE_CID) with 128; lia|].
      split.
      { intros a Ha. split; [|unfold NX_STK, AFREAD_STK; lia].
        right; right; right. exists PE_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [frame_rng fst snd].
        rewrite EF. change (fs_frame_bytes PE_CID) with 128. lia. }
      split.
      { apply (h_ra_frame (w_H W3) mem (pF cx fp) (pSH cx fp) 96 8 ESH HF64); [lia | reflexivity | lia |].
        intros j Hj. change ((8 + 7) / 8) with 1 in Hj. change (96 / 8) with 12.
        assert (j = 0) as -> by lia. rewrite Z.add_0_r.
        change (pSH cx fp + 12) with (pSH cx fp + Z.of_nat 12). rewrite SHm by lia. reflexivity. }
      unfold nx_bufn, PS_LEN. fold (p_bn cx). split; dlia1 Dbuf.
    - intros _. rewrite HLC. unfold nx_bufn, PS_LEN. fold (p_bn cx).
      split; [exact Hh_in|]. split; [exact Hb_in|].
      split.
      { apply (asource_at_frame KS (rdW W3 (ms_mem ms3)) (rdW W3 mem) h b (p_C cx) 24); [|exact HSRC].
        intros a Ha. rewrite HLC in Ha. unfold SRC_FILE_BLOCK in Ha.
        destruct Ha as [Ha | [Ha | Ha]].
        - apply MK; dlia2 Dh Hhapp.
        - apply MK; dlia2 Db Hbapp.
        - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _).
          pose proof (pa_img_range a Hi) as Hr1. pose proof (pa_segs_low a Hi) as Hr2.
          unfold pcap_img_end, YImgTop.IMG_TOP, kLowMemEnd in Hr1, Hr2. apply MK; dlia1 HFimg. }
      unfold SRC_FILE_BLOCK. split; [lia|]. split; [lia|].
      split; [dlia1 Dhbuf|]. split; [dlia1 Dbbuf|]. split; [dlia1 Dh|]. split; [dlia1 Db|].
      split; [intros _; split; [dlia1 Dh | dlia1 Db]|].
      intros x Hx. destruct (in_asource_fp h x Hx) as [Hx1 | Hx0].
      + right. exists h, SRC_FILE_BLOCK. split; [exact Hh_in|]. split; [exact Hh_fr|].
        change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx1. lia.
      + left. exists YI16.sink_token. split; [left; reflexivity | unfold YI16.sink_token; cbn [fst snd]; lia].
    - intros _. exact (h_meta_gx cx memS' [(PE_CID, fp)] ly3 S3 W3 mem _ k HB HJm HAGm). }
  (* ---- back from pcap_source_next, at 0x80af4 ---- *)
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HPR & HBL & HFR2 & HMO2 & Hfds2 & Hfs2 & HFIN).
  subst c2.
  destruct HFIN as [(Hh0 & _) | (_ & Er & HK & HSRC2 & HPS2 & (bj' & HBJ2 & Hbjl' & Hpre) & HTS2)]; [lia|].
  destruct HK as (K1 & K2 & K3 & K4 & _ & _).
  rewrite Esp in K1.
  assert (NW : forall a, ~ ((pF cx fp + 32 <= a < pF cx fp + 56) \/ (buf <= a < buf + p_bn cx) \/
        (pF cx fp + 96 <= a < pF cx fp + 104) \/ (h <= a < h + 1304)) ->
      ~ nx_wrset (pF cx fp + 32) buf (p_cap cx) (pF cx fp + 96) h a).
  { intros a Hn Hc. apply Hn. unfold nx_wrset, nx_bufn, PS_LEN, SRC_FILE_BLOCK in Hc. fold (p_bn cx) in Hc. lia. }
  (* the stack above the slots, as at the cut *)
  assert (KH : forall a, c_sp1 cx + 96 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite K1; [apply KR; lia | lia | lia | apply NW; lia]. }
  (* the slots, as the run left them *)
  assert (KSL : forall a, c_sp1 cx <= a < c_sp1 cx + 96 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem a).
  { intros a Ha. apply K1; [lia | lia | apply NW; lia]. }
  (* the frame outside ps and ts, as at the cut *)
  assert (KF : forall a, (pF cx fp <= a < pF cx fp + 32) \/ (pF cx fp + 56 <= a < pF cx fp + 96) \/
      (pF cx fp + 104 <= a < pF cx fp + 128) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite (K4 PE_CID fp a Hfin).
    - apply KR; lia.
    - left. unfold in_zr. cbn [frame_rng fst snd]. rewrite EF. change (fs_frame_bytes PE_CID) with 128. lia.
    - apply NW; dlia2 Dbuf Dh. }
  (* the frame's shadow, as the run left it *)
  assert (KSH : forall i, (i < 16)%nat -> aview SEGS (w_H W2) mem2 (pSH cx fp + Z.of_nat i) = Some (nth i PSH_ts 0)).
  { intros i Hi. rewrite (K4 PE_CID fp (pSH cx fp + Z.of_nat i) Hfin).
    - exact (SHm i Hi).
    - right. unfold in_zr. cbn [fst snd].
      replace (shadow_addr (frame_addr ly3 PE_CID fp)) with (pSH cx fp) by (rewrite EF, ESH; unfold shadow_addr; reflexivity).
      change (fs_frame_bytes PE_CID / 8) with 16. lia.
    - apply NW. dlia2 Hbufapp Hhapp. }
  (* the harness's globals, as at the cut *)
  assert (KG : forall a, inG pe_G a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Hin. destruct (HG a Hin) as [Hi Hns]. destruct (HGR a Hin) as (_ & _ & Her & _).
    pose proof (pa_img_range a Hi) as Hr1. pose proof (pa_segs_low a Hi) as Hr2.
    unfold pcap_img_end, YImgTop.IMG_TOP, kLowMemEnd in Hr1, Hr2.
    rewrite (K3 a Hi Hns Her). apply KR; dlia1 HFimg. }
  destruct (h_nx_model cx 24) as (Nq & Nlh & Nres & Npos & Nkind & NF).
  apply (HKD cx fp (k + EV_NEXT) (acc + 0) ly2 S2 W2 (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 HB).
  { eapply ajournal_gx_pack; [unfold LLVMF_STK; lia | lia | | exact HAGm | intros a Ha _; lia].
    rewrite (Z.add_0_r LLVMF_STK), (Z.add_0_r (spZ (c_regs cx))). exact HJ2. }
  { rewrite HFR2. exact HFR. }
  { exact (mo_le_trans MT MTL _ _ _ _ _ HMO HMO2). }
  exists b, h, buf.
  split.
  { unfold p_cut. split.
    2:{ split; [unfold EV_NEXT; lia|]. split; [lia|]. split; [rewrite HBL; exact HPERM|].
        split; [rewrite Hfds2, Hfdsc; exact Hfds | rewrite Hfs2, Hfsc; exact Hfs]. }
    unfold pe_body, pregs, psaved, pheader, pshadow.
    cbn [ms_mem ms_regs ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    split; [rewrite Q1; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { rewrite !(h_pres _ _ _ HPR) by acs.
      split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q27|]. split; [exact Q3 | exact Q4]. }
    split.
    { split.
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KH; lia | exact (proj1 HSAVED)].
      - intros j Hj. apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KH; lia|].
        exact (proj2 HSAVED j Hj). }
    split.
    { destruct HHDR as (HH0 & HH8 & HH16 & HH120).
      split; [|split; [|split]].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KF; lia | exact HH0].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KF; lia | exact HH8].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KF; lia | exact HH16].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KF; unfold PE_FLAGPTR; lia | exact HH120]. }
    split; [intros i Hi; change (length PSH_ts) with 16%nat in Hi; exact (KSH i Hi)|].
    split; [reflexivity|].
    { apply (garr8_frame SEGS (rdW W3 (ms_mem ms3)) (rdW W2 mem2) _ _ HIN). intros a Ha. rewrite length_map in Ha.
      apply (mbyte_of_aview SEGS).
      destruct HINP as [(Hn0 & _) | (Hn & Hinc)]; [unfold c_n in Hn0; lia|].
      assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hinc).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & Hpapp & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreqp].
      pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3 Hfin) as Dp.
      rewrite EF in Dp. change (fs_frame_bytes PE_CID) with 128 in Dp.
      assert (Dpbuf : zdisjoint (c_p cx, req_size (c_n cx)) (buf, req_size (p_bn cx))).
      { apply (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3 Hbuf_in). intros E'. apply Hbuf_fr. rewrite <- E'. exact Hinc. }
      assert (Dph : zdisjoint (c_p cx, req_size (c_n cx)) (h, req_size SRC_FILE_BLOCK)).
      { apply (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3 Hh_in). intros E'. apply Hh_fr. rewrite <- E'. exact Hinc. }
      change (req_size SRC_FILE_BLOCK) with 1304 in Dph.
      unfold c_n in *.
      replace a with (c_p cx + (a - c_p cx)) by lia.
      rewrite (K2 (c_p cx) _ (a - c_p cx) Hin3 ltac:(lia)); [apply KR; dlia2 Dp Hpapp|]. apply NW. dlia3 Dp Dpbuf Dph. } }
  split; [unfold p_pspad, pPS, PO_PS; cbn [ms_mem mkst]; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPS2))))))|].
  split; [exact Hn26|]. split; [exact Hgood|].
  cbn [ms_mem ms_regs mkst].
  split; [rewrite Er; unfold p_first; rewrite Nres; reflexivity|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q19|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q21|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q22|].
  split.
  { unfold pslots, pslot, PS_PSP, PS_GLEN, PS_D, PS_SH, PS_F, PS_FK, PS_TSP, pPS, PO_PS, PO_TS. cbn [ms_mem mkst].
    split; [apply (h_rdword_keep (w_H W3) (w_H W2) mem mem2); [intros i Hi; apply KSL; lia | exact SLpsp]|].
    split; [apply (h_rdword_keep (w_H W3) (w_H W2) mem mem2); [intros i Hi; apply KSL; lia | exact SLglen]|].
    split; [apply (h_rdword_keep (w_H W3) (w_H W2) mem mem2); [intros i Hi; apply KSL; lia | exact SLd]|].
    split; [apply (h_rdword_keep (w_H W3) (w_H W2) mem mem2); [intros i Hi; apply KSL; lia | exact SLsh]|].
    split; [apply (h_rdword_keep (w_H W3) (w_H W2) mem mem2); [intros i Hi; apply KSL; lia | exact SLf]|].
    split; [apply (h_rdword_keep (w_H W3) (w_H W2) mem mem2); [intros i Hi; apply KSL; lia | exact SLfk]|].
    apply (h_rdword_keep (w_H W3) (w_H W2) mem mem2); [intros i Hi; apply KSL; lia | exact SLts]. }
  split.
  { unfold p_glob, pval. split.
    - eapply vm_frame; [|exact (proj1 HGL)]. intros x Hx. apply (mbyte_of_aview SEGS). apply KG.
      apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. change (Z.of_nat 8) with 8 in Hx. lia.
    - eapply vm_frame; [|exact (proj2 HGL)]. intros x Hx. apply (mbyte_of_aview SEGS). apply KG.
      apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. change (Z.of_nat 8) with 8 in Hx. lia. }
  { unfold p_reader, p_psopen, pval, pPS, pTS, PO_PS, PO_TS. cbv zeta. cbn [ms_mem mkst].
    rewrite Npos in HSRC2.
    destruct HPS2 as (P0 & P8 & P12 & P16 & P20 & _ & _).
    unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in P0, P8, P12, P16, P20.
    rewrite Z.add_0_r in P0.
    split; [exact HSRC2|]. split; [split; [exact P0 | exact P8]|].
    intros HKf.
    assert (Hlh : PSN.psn_lh (p_sw cx) (p_F cx) (p_cap cx) 24 = Some (p_q cx 24)) by (apply h_psn_lh_fit; [lia | exact HKf]).
    assert (Hfit : nx_fit (p_swz cx =? 1) (p_C cx) (p_cap cx) 24 = true) by (unfold nx_fit; rewrite Nkind, HKf; reflexivity).
    unfold nx_orig in P12. rewrite Nlh, Hlh, NF in P12.
    unfold nx_vtag in P16. rewrite Hfit, Nq, NF in P16.
    unfold nx_vid in P20. rewrite Hfit, Nq, NF in P20.
    specialize (HTS2 ltac:(lia)). unfold nx_tsv in HTS2. rewrite Hfit, Nq, NF in HTS2.
    specialize (Hpre Hfit).
    rewrite <- (firstn_skipn (length (nx_rec (p_swz cx =? 1) (p_C cx) (p_cap cx) 24)) bj') in HBJ2.
    apply (garr8_app SEGS) in HBJ2. destruct HBJ2 as [HBJa _]. rewrite Hpre in HBJa. unfold nx_rec in HBJa.
    rewrite Nq, NF in HBJa.
    split; [exact P12|]. split; [exact P16|]. split; [exact P20|]. split; [exact HTS2 | exact HBJa]. }
Qed.

(* ---- walk C ---- *)
Theorem pe_C : forall POST, pe_from SK B MT KS POST (GI_KD B MT KS) -> pe_from SK B MT KS POST (GI_K3 B MT KS).
Proof.
  intros POST HKD cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  pose proof HJ as HJ0.
  destruct HI as (b & h & buf & HCUT & Hn26 & Hgood & Hbuf4096 &
                  R10 & R19 & R20 & R21 & R23 & R25 & SD & SGLEN & SPSP & HGL & HPSO & HPSF & HSRC).
  pose proof HCUT as (HBODY & Hk & Hacc & HPERM & Hfds & Hfs).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G27 & G3 & G4) & HSAVED & HHDR & HSH &
                       Hlen & HIN).
  pose proof (h_sp cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  destruct (h_base cx HB) as (HROD & HMETA & HG & HGR).
  pose proof HJ as HJgx. destruct HJ as (_ & _ & (memS & HJ & HAG) & _). rewrite !Z.add_0_r in HJ.
  pose proof (h_frame cx fp memS ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR)
    as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof (p_d_range cx) as Hd.
  pose proof (h_blocks3 ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ HAR3 HPERM)
    as (Hb_in & Hh_in & Hbuf_in & Hb_fr & Hh_fr & Hbuf_fr & Dbh & Dbbuf & Dhbuf).
  cbn [fst snd] in Dbh, Dbbuf, Dhbuf.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hh_in) as (_ & Hh4096 & Hhceil & Hhapp & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbuf_in) as (Hbuf16 & _ & Hbufceil & Hbufapp & _ & _ & _).
  pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hreqbn].
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil, Dbh, Dhbuf.
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hbuf_in Hfin) as Dbuf.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hh_in Hfin) as Dh.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hb_in Hfin) as Db.
  rewrite EF in Dbuf, Dh, Db. change (fs_frame_bytes PE_CID) with 128 in Dbuf, Dh, Db.
  change (req_size SRC_FILE_BLOCK) with 1304 in Dh, Hhapp.
  assert (HSHr : SB + 512 <= pSH cx fp /\ pSH cx fp + 16 <= SB + 2 ^ 44 /\ pSH cx fp mod 8 = 0).
  { destruct (h_div8_of_mul64 (pF cx fp) HF64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF, SB.
    pose proof (Z.div_lt_upper_bound (pF cx fp + 128) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_lower_bound (pF cx fp) 8 512 ltac:(lia) ltac:(lia)).
    replace ((pF cx fp + 128) / 8) with (pF cx fp / 8 + 16) in H
      by (rewrite <- (Z.div_add (pF cx fp) 16 8) by lia; f_equal; lia).
    split; [lia|]. split; [lia|].
    rewrite E8. replace (2147450880 + 8 * (pF cx fp / 64)) with ((268431360 + pF cx fp / 64) * 8) by lia.
    apply Z_mod_mult. }
  unfold SB in HSHr.
  (* the frame lies in application memory, its shadow in the shadow band *)
  assert (DFSH : pF cx fp + 128 <= pSH cx fp \/ pSH cx fp + 16 <= pF cx fp).
  { clear - HFapp HSHr C1 C3. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
  remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (p_d cx)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
    by (intros q r Hq; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (E32 : ew E 32 = Z_to_bv 64 (p_d cx))
    by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply h_w64_unsigned; lia).
  assert (U23 : bv_unsigned (ew E 23) = pF cx fp) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply h_w64_unsigned; lia).
  assert (U25 : bv_unsigned (ew E 25) = pSH cx fp) by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply h_w64_unsigned; lia).
  assert (U10 : bv_unsigned (ew E 10) = buf) by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply h_w64_unsigned; lia).
  (* the symbolic state at 0x80abc *)
  assert (HS : st_ok_pi SEGS VAL E hss_C (restrict (w_H W3) ms3)).
  { rewrite (h_restrict_body cx fp PP_K3 W3 ms3 PSH_ps HBODY). unfold hss_C.
    apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      + unfold region_ok, hR_slotsC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LLVMF_STK. lia. }
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        * apply (h_slot_chunk_ok E (w_H W3) (ms_mem ms3) (c_sp1 cx) 32 (SOff 32 0) (p_d cx)); [exact SD | | lia].
          rewrite h_denot_off0. exact E32.
        * apply (h_slot_chunk_ok E (w_H W3) (ms_mem ms3) (c_sp1 cx) 64 (SOff (A_HI 8) 0) (VAL (A_HI 8))); [exact SGLEN | |].
          { rewrite h_denot_off0. apply (img_env_atomP E (A_HI 8) HEI). unfold A_HI, A_TEXT, A_LIM. lia. }
          { apply pa_val_range. }
        * apply (h_slot_chunk_ok E (w_H W3) (ms_mem ms3) (c_sp1 cx) 88 (SOff 23 32) (pF cx fp + 32)); [exact SPSP | | lia].
          apply (h_denot_off E 23 (pF cx fp) 32); [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia].
      + unfold region_ok, hR_shC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U25. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (apresent_writable SEGS). apply HSHpres. lia. }
        apply hsh_chunks_ok. intros j Hj. rewrite Z.add_0_l. exact (HSH j Hj).
      + unfold region_ok, hR_tsC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U23. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply HFpres. lia.
    - apply pairwise_disjoint_of_extents.
      unfold hR_slotsC, hR_shC, hR_tsC, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U9, U23, U25. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hsp1 Hsp_lo C1 HFceil HF4096 HSHr DFSH. repeat split; lia.
    - split; [|split; exact I]. cbn [hfacts_C f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U10, U23, U25. unfold SB.
      repeat match goal with |- _ /\ _ => split end;
        first [ lia | (change (2 ^ 5) with 32; exact Hsp1_32) | (change (2 ^ 4) with 16; exact Hbuf16)
              | (change (2 ^ 6) with 64; exact HF64) | (change (2 ^ 3) with 8; exact (proj2 (proj2 HSHr))) ]. }
  assert (SHOK : sh_ok SEGS (SLit SB) [] E (rdW W3 (ms_mem ms3))) by constructor.
  pose (RUNX := paj_run_x B LAWS pe_G HG 0 []).
  clear HJ. rename HJgx into HJ.
  paj_run_tok RUNX HS HJ SHOK hBspan0.
  { apply awr_ok_x_of0.
    lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 25%nat (pSH cx fp)); [reflexivity | exact U25 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists PE_CID, fp.
      split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
      replace (shadow_addr (frame_addr ly3 PE_CID fp)) with (pSH cx fp) by (rewrite EF, ESH; unfold shadow_addr; reflexivity).
      change (fs_frame_bytes PE_CID / 8) with 16. lia. }
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (pF cx fp)); [reflexivity | exact U23 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists PE_CID, fp.
      split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EF.
      change (fs_frame_bytes PE_CID) with 128. lia. }
    apply awr_ok_nil. }
  (* ---- at the call of pcap_source_next, 0x80af0 ---- *)
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
  rewrite U23 in Q10, Q13.
  rewrite (EE 2%nat 2%bv eq_refl), G2 in Q2. rewrite (EE 3%nat 3%bv eq_refl), G3 in Q3.
  rewrite (EE 4%nat 4%bv eq_refl), G4 in Q4. rewrite (EE 8%nat 8%bv eq_refl), G8 in Q8.
  rewrite (EE 9%nat 9%bv eq_refl), G9 in Q9. rewrite (EE 10%nat 10%bv eq_refl), R10 in Q11, Q22.
  rewrite (EE 21%nat 21%bv eq_refl), R21 in Q12, Q21. rewrite (EE 19%nat 19%bv eq_refl), R19 in Q19.
  rewrite (EE 27%nat 27%bv eq_refl), G27 in Q27.
  assert (Esp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2; apply h_w64_unsigned; lia).
  assert (Es0 : s0Z (ms_regs ms) = spZ (c_regs cx)) by (unfold s0Z; rewrite Q8; apply h_w64_unsigned; lia).
  (* what the run wrote: the slots, shadow byte 12 and ts; everything else is as at the cut *)
  assert (KR : forall a, 0 <= a < 2 ^ 64 ->
     ~ ((c_sp1 cx <= a < c_sp1 cx + 96) \/ (pSH cx fp + 12 <= a < pSH cx fp + 13) \/ (pF cx fp + 96 <= a < pF cx fp + 104)) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { apply (kept_of_frame (segs := SEGS) E (ss_mem hss_C) (w_H W3) (ms_mem ms3) (ms_mem ms) _ HFr).
    intros bb wlo whi a Hin Ha. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?U9, ?U25, ?U23 in Ha; lia |]).
    destruct Hin. }
  assert (MK : forall a, 0 <= a < 2 ^ 64 ->
     ~ ((c_sp1 cx <= a < c_sp1 cx + 96) \/ (pSH cx fp + 12 <= a < pSH cx fp + 13) \/ (pF cx fp + 96 <= a < pF cx fp + 104)) ->
     mbyte SEGS (rdW W3 (ms_mem ms)) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a)
    by (intros a Ha Hn; apply (mbyte_of_aview SEGS); exact (KR a Ha Hn)).
  assert (VS : forall od e v, In (YP09.mkChunk od (CVal 8 e))
      [YP09.mkChunk 80 (CVal 8 (SOff 23 96)); YP09.mkChunk 8 (CVal 8 (SOff 25 0));
       YP09.mkChunk 16 (CVal 8 (SOff 23 0)); YP09.mkChunk 24 (CVal 8 (SOff 20 0));
       YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff 288 0));
       YP09.mkChunk 88 (CVal 8 (SOff 23 32))] ->
      sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
      rdword (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx + od) = Some v).
  { intros od e v Hin He Hv. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|exact Hv].
    refine (h_field E _ (restrict (w_H W3) ms) 0 9 0 96 0 96 _ (c_sp1 cx) od 8 e v HS eq_refl U9 Hin He _ _);
      cbn; lia. }
  assert (SHm : forall i, (i < 16)%nat ->
      aview SEGS (w_H W3) (ms_mem ms) (pSH cx fp + Z.of_nat i) = Some (nth i PSH_ts 0)).
  { intros i Hi. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms)); [|apply PSH_ts_range].
    refine (h_field E _ (restrict (w_H W3) ms) 1 25 0 16 12 13 _ (pSH cx fp) (Z.of_nat i) 1
      (SLit (nth i PSH_ts 0)) (nth i PSH_ts 0) HS eq_refl U25 _ eq_refl _ _).
    - do 16 (destruct i as [|i]; [cbn; tauto|]). lia.
    - change (2 ^ (8 * Z.of_N 1)) with 256. exact (PSH_ts_range i).
    - cbn. lia. }
  assert (TSm : val_mem SEGS (rdW W3 (ms_mem ms)) (pF cx fp + 96) 8 18446744073709551615).
  { refine (h_field E _ (restrict (w_H W3) ms) 2 23 96 104 96 104 _ (pF cx fp) 96 8
      (SLit 18446744073709551615) 18446744073709551615 HS eq_refl U23 _ eq_refl _ _); cbn; [tauto | lia | lia]. }
  pmkst HS. rewrite pa_sigma_pcap_source_next.
  refine (h_C_next POST HKD cx fp k acc ly3 S3 W3 ms3 md3 b h buf (ms_regs ms) (ms_mem ms) _ HB HJ0 HFR HMO HCUT Hn26 Hgood
    R20 HGL HPSO HPSF HSRC HJ (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))
    Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q13 Q19 Q21 Q22 Q27 KR _ _ _ _ _ _ _ SHm TSm).
  - apply (VS 88 (SOff 23 32)); [cbn; tauto | apply (h_denot_off E 23 (pF cx fp) 32); [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia] | lia].
  - apply (VS 64 (SOff 288 0)); [cbn; tauto | | apply pa_val_range].
    rewrite h_denot_off0. apply (img_env_atomP E (A_HI 8) HEI). unfold A_HI, A_TEXT, A_LIM. lia.
  - apply (VS 32 (SOff 32 0)); [cbn; tauto | rewrite h_denot_off0; exact E32 | lia].
  - apply (VS 8 (SOff 25 0)); [cbn; tauto | rewrite h_denot_off0, (EE 25%nat 25%bv eq_refl); exact R25 | lia].
  - apply (VS 16 (SOff 23 0)); [cbn; tauto | rewrite h_denot_off0, (EE 23%nat 23%bv eq_refl); exact R23 | lia].
  - apply (VS 24 (SOff 20 0)); [cbn; tauto | rewrite h_denot_off0, (EE 20%nat 20%bv eq_refl); exact R20 | lia].
  - apply (VS 80 (SOff 23 96)); [cbn; tauto | apply (h_denot_off E 23 (pF cx fp) 96); [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia] | lia].
Qed.






(* ---- walk B, the accepted arm's malloc (0x80ab8) and the return to PP_K3 (0x80abc) ---- *)
Hypothesis AM : amalloc04_rule SEGS B MT.
Hypothesis AF : afree04_rule SEGS B MT.

Lemma h_B_malloc : forall POST, pe_from SK B MT KS POST (GI_K3 B MT KS) ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b h (regs : bvmap 5 word) mem mdc,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  pe_body cx fp PP_K2 W3 ms3 PSH_ps -> c_n cx < 2 ^ 26 ->
  m_fds md3 = m_fds (c_md cx) -> m_fs md3 = m_fs (c_md cx) ->
  pslot cx W3 ms3 PS_D (p_d cx) -> pslot cx W3 ms3 PS_GLEN (VAL (A_HI 8)) -> pslot cx W3 ms3 PS_PSP (pPS cx fp) ->
  p_glob cx W3 ms3 b ->
  p_good cx = true -> k <= 2 -> acc <= PA_K2g MT cx ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK)]) ->
  p_psopen cx fp W3 ms3 h -> p_psfresh cx fp W3 ms3 -> asource_at SEGS KS (rdW W3 (ms_mem ms3)) h b (p_C cx) 24 ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem mdc k ->
  m_fds mdc = m_fds md3 -> m_fs mdc = m_fs md3 ->
  getr regs 1 = Z_to_bv 64 (BASE + 900) -> getr regs 2 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) -> getr regs 10 = w64 (p_bn cx) ->
  getr regs 19 = w64 b -> getr regs 20 = w64 (pF cx fp) -> getr regs 21 = w64 (p_cap cx) ->
  getr regs 23 = w64 (pF cx fp) -> getr regs 25 = w64 (pSH cx fp) -> getr regs 27 = w64 SHADOW_OFF ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (pc_wrap_malloc (as_code B))) mem (seg_rom SEGS)) mdc) (POST cx).
Proof.
  intros POST HK3 cx fp k acc ly3 S3 W3 ms3 md3 b h regs mem mdc HB HJ HFR HMO HBODY Hn26 Hfds Hfs SD SGLEN SPSP HGL
    Hgood Hk Hacc HPERM HPSO HPSF HSRC HJc Hfdsc Hfsc Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q19 Q20 Q21 Q23 Q25 Q27 KR.
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G27 & G3 & G4) & HSAVED & HHDR & HSH &
                       Hlen & HIN).
  pose proof (h_sp cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  destruct (h_base cx HB) as (HROD & HMETA & HG & HGR).
  destruct HJ as (_ & _ & (memS & HJ & HAG) & _). rewrite !Z.add_0_r in HJ.
  pose proof (h_frame cx fp memS ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR)
    as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof (p_d_range cx) as Hd.
  pose proof HB as ((_ & _ & Hra4 & Hgp0 & Htp0 & _) & _ & _ & _ & HINP & _ & _ & Hnev0 & Hlive0 & _ & _ & _ & _ & _ & _ & _ &
                    HMOK & Hneed & _ & _ & _ & HTRm & HTRf).
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (HSHr : SB + 512 <= pSH cx fp /\ pSH cx fp + 16 <= SB + 2 ^ 44 /\ pSH cx fp mod 8 = 0).
  { destruct (h_div8_of_mul64 (pF cx fp) HF64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF, SB.
    pose proof (Z.div_lt_upper_bound (pF cx fp + 128) 8 (2 ^ 44) ltac:(dlia1 HFapp) ltac:(lia)).
    pose proof (Z.div_le_lower_bound (pF cx fp) 8 512 ltac:(lia) ltac:(lia)).
    replace ((pF cx fp + 128) / 8) with (pF cx fp / 8 + 16) in H
      by (rewrite <- (Z.div_add (pF cx fp) 16 8) by lia; f_equal; lia).
    split; [lia|]. split; [lia|].
    rewrite E8. replace (2147450880 + 8 * (pF cx fp / 64)) with ((268431360 + pF cx fp / 64) * 8) by lia.
    apply Z_mod_mult. }
  unfold SB in HSHr.
  assert (DFSH : pF cx fp + 128 <= pSH cx fp \/ pSH cx fp + 16 <= pF cx fp)
    by (clear - HFapp HSHr C1 C3; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia).
  destruct HJc as (_ & _ & (memS' & HJm & HAGm) & _). rewrite !Z.add_0_r in HJm.
  pose proof HJm as (HARm & _).
  assert (Esp : spZ regs = c_sp1 cx) by (unfold spZ; rewrite Q2; apply h_w64_unsigned; lia).
  assert (Es0 : s0Z regs = spZ (c_regs cx)) by (unfold s0Z; rewrite Q8; apply h_w64_unsigned; lia).
  assert (Era : raZ regs = BASE + 900).
  { unfold raZ. rewrite Q1, unsigned_lit_small; [reflexivity|]. pose proof pa_base_lo. pose proof pa_B_ok. lia. }
  pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HBok.
  (* the room of the call *)
  assert (Hbb : blocks_bytes S3 + p_bn cx <= LIVE_MAX).
  { rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPERM), bsum_app. cbn [bsum fold_right fst snd].
    rewrite <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). unfold LIVE_LIB, SRC_FILE_BLOCK in *. unfold c_n in Hn26.
    unfold p_nF in *. lia. }
  assert (Hmo : mo_ok MT S3 (mo_malloc MT (p_bn cx))).
  { pose proof (PA_K12_need MT MTL cx) as HN.
    pose proof (mo_malloc_nonneg MT MTL SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as N1.
    pose proof (mo_free_nonneg MT MTL) as N3.
    apply (mo_ok_le MT MTL S3 _ (c_T cx - acc)); [|unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g, PA_K1 in *; lia].
    apply (mo_ok_step MT MTL (c_S cx) S3 acc (c_T cx - acc)); [|exact HMO].
    replace (acc + (c_T cx - acc)) with (c_T cx) by lia. exact HMOK. }
  eapply SRr_bind.
  { eapply (amalloc04_sub_fs SK SEGS B LAWS pa_segs_low MT AM W3 regs mem LLVMF_STK (spZ (c_regs cx)) [sink_token]
      (c_ly cx) (c_S cx) (c_W cx) memS' (c_md cx) [(PE_CID, fp)] ly3 S3 mdc k (p_bn cx) (c_sp1 cx - spZ (c_regs cx))
      (Z_to_bv 64 (BASE + 900)) (pch cx) HJm Q10).
    - unfold MALLOC_MAX. lia.
    - exact Hbb.
    - rewrite Esp. lia.
    - replace (c_sp1 cx - spZ (c_regs cx)) with ((c_sp1 cx / 16 - spZ (c_regs cx) / 16) * 16)
        by (pose proof (h_mod32_8 _ Hsp1_32) as [M16 _]; pose proof (Z_div_mod_eq_full (c_sp1 cx) 16);
            pose proof (Z_div_mod_eq_full (spZ (c_regs cx)) 16); lia).
      apply Z.mod_mul. lia.
    - lia.
    - unfold ASTACK, LLVMF_STK. lia.
    - rewrite Q3. exact Hgp0.
    - rewrite Q4. exact Htp0.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold EV_LIB in *. lia.
    - apply (achain_chain_pre ly3 (aview SEGS (w_H W3) mem) (c_sp1 cx) (spZ (c_regs cx)) (pch cx) regs).
      + apply (h_achain cx memS' ly3 S3 W3 mem _ [(PE_CID, fp)] k (c_sp1 cx) HB HJm HAGm).
        * apply (h_rdword_keep (w_H W3) (w_H W3) (ms_mem ms3) mem); [|exact (proj1 HSAVED)].
          intros i Hi. apply KR; lia.
        * pose proof (proj2 HSAVED 0 ltac:(lia)) as HS0. rewrite Z.mul_0_r, Z.sub_0_r in HS0.
          apply (h_rdword_keep (w_H W3) (w_H W3) (ms_mem ms3) mem); [|exact HS0].
          intros i Hi. apply KR; lia.
        * lia.
      + rewrite Esp. lia.
      + exact Es0.
      + rewrite Era. lia.
    - apply HTRm. rewrite Era. replace (BASE + 900 - BASE) with 900 by lia. cbn. right. left. reflexivity.
    - exact Hmo. }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & res & Ec & HJ2 & HPR & Hres & Hfr2 & Hr4 & Hbl & HK & MLE &
                                Hfd2 & Hfs2).
  subst c2. destruct HK as (K1 & K2 & K3 & K4 & _ & _).
  pose proof HJ2 as (HAR2 & Hly2 & _).
  assert (EF2 : frame_addr ly2 PE_CID fp = pF cx fp).
  { pose proof HB as ((HAR0 & _) & _). destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR0 Hly2) as (_ & Efa & _).
    unfold pF. apply Efa. }
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in K1 by lia.
  assert (Hnew : In (res, p_bn cx) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  assert (Hfresh : ~ In (res, p_bn cx) (ablocks B ly3 S3)).
  { pose proof (h_ablocks_nodup ly2 S2 W2 mem2 md2 HAR2) as Hnd. rewrite Hbl in Hnd.
    exact (h_nodup_app_disj _ _ _ _ Hnd (or_introl eq_refl)). }
  assert (Hfin2 : In (PE_CID, fp) (frames S2)) by (rewrite Hfr2; exact Hfin).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hnew Hfin2) as Dnew.
  rewrite EF2 in Dnew. change (fs_frame_bytes PE_CID) with 128 in Dnew.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hnew) as (_ & _ & Hnceil & Hnapp & _ & _ & _).
  pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hreqbn].
  (* what the call kept: the caller's blocks, the frame and its shadow, the stack above the call's window, the image *)
  assert (KB : forall p m i, In (p, m) (ablocks B ly3 S3) -> 0 <= i < req_size m ->
     aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W3) (ms_mem ms3) (p + i)).
  { intros p m i Hin Hi.
    assert (Hin2 : In (p, m) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hin).
    assert (Hne : (p, m) <> (res, p_bn cx)) by (intros E'; apply Hfresh; rewrite <- E'; exact Hin).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hin2 Hnew Hne) as D.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
    rewrite (K2 p m i Hin Hi); [apply KR; lia|]. cbn beta. dlia1 D. }
  assert (KF : forall a, (pF cx fp <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite (K4 PE_CID fp a Hfin).
    - apply KR. lia.
    - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr; cbn [frame_rng fst snd];
        [rewrite EF; change (fs_frame_bytes PE_CID) with 128; lia|].
      replace (shadow_addr (frame_addr ly3 PE_CID fp)) with (pSH cx fp) by (rewrite EF, ESH; unfold shadow_addr; reflexivity).
      change (fs_frame_bytes PE_CID / 8) with 16. lia.
    - cbn beta. destruct Ha as [Ha | Ha]; [dlia1 Dnew | dlia1 Hnapp]. }
  assert (KH : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite K1; [apply KR; lia | lia | lia]. }
  assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Hi Hns Her. rewrite (K3 a Hi Hns Her). apply KR. exact (h_img_range a Hi). }
  assert (Hb_in : In (b, p_nF cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; left; reflexivity).
  assert (Hh_in : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; right; left; reflexivity).
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
  apply (HK3 cx fp (k + 1) (acc + mo_malloc MT (p_bn cx)) ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + 900)) mem2 (seg_rom SEGS))
           md2 HB).
  { eapply ajournal_gx_pack; [unfold LLVMF_STK; lia | lia | | exact HAGm | intros a Ha _; lia].
    rewrite (Z.add_0_r LLVMF_STK), (Z.add_0_r (spZ (c_regs cx))). exact HJ2. }
  { rewrite Hfr2. exact HFR. }
  { exact (mo_le_trans MT MTL _ _ _ _ _ HMO MLE). }
  exists b, h, res.
  split.
  { unfold p_cut. split.
    2:{ split; [lia|]. split; [unfold PA_K3; lia|].
        split; [rewrite Hbl; change (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK); (res, p_bn cx)])
                  with (ablocks B (c_ly cx) (c_S cx) ++ ([(b, p_nF cx); (h, SRC_FILE_BLOCK)] ++ [(res, p_bn cx)]));
                rewrite app_assoc; apply Permutation_app_tail; exact HPERM|].
        split; [rewrite Hfd2, Hfdsc; exact Hfds | rewrite Hfs2, Hfsc; exact Hfs]. }
    unfold pe_body, pregs, psaved, pheader, pshadow.
    cbn [ms_mem ms_regs ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { rewrite !(h_pres _ _ _ HPR) by acs.
      split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q27|]. split; [exact Q3 | exact Q4]. }
    split.
    { split.
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KH; lia | exact (proj1 HSAVED)].
      - intros j Hj. apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KH; lia|].
        exact (proj2 HSAVED j Hj). }
    split.
    { destruct HHDR as (HH0 & HH8 & HH16 & HH120).
      split; [|split; [|split]].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KF; lia | exact HH0].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KF; lia | exact HH8].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KF; lia | exact HH16].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KF; unfold PE_FLAGPTR; lia | exact HH120]. }
    split; [intros i Hi; rewrite KF; [exact (HSH i Hi) | change (length PSH_ps) with 16%nat in Hi; lia]|].
    split; [reflexivity|].
    { apply (garr8_frame SEGS (rdW W3 (ms_mem ms3)) (rdW W2 mem2) _ _ HIN). intros a Ha. rewrite length_map in Ha.
      apply (mbyte_of_aview SEGS).
      destruct HINP as [(Hn0 & _) | (Hn & Hinc)]; [unfold c_n in Hn0; lia|].
      assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hinc).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreqp].
      unfold c_n in *. replace a with (c_p cx + (a - c_p cx)) by lia. apply (KB _ _ _ Hin3). lia. } }
  cbn [ms_mem ms_regs mkst].
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hr4|]. split; [exact Hres|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q19|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q20|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q21|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q23|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q25|].
  unfold pslot in SD, SGLEN, SPSP.
  split; [unfold pslot; apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KH; unfold PS_D; lia | exact SD]|].
  split; [unfold pslot; apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KH; unfold PS_GLEN; lia | exact SGLEN]|].
  split; [unfold pslot; apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i Hi; apply KH; unfold PS_PSP; lia | exact SPSP]|].
  split.
  { unfold p_glob, pval in *. destruct HGL as (HGL2 & HGL4). split.
    - eapply vm_frame; [|exact HGL2]. intros x Hx. apply (mbyte_of_aview SEGS).
      assert (Hin : inG pe_G x) by (apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
        change (Z.of_nat 8) with 8 in Hx; lia).
      destruct (HG x Hin) as [Hi Hns]. destruct (HGR x Hin) as (_ & _ & Her & _). exact (KI x Hi Hns Her).
    - eapply vm_frame; [|exact HGL4]. intros x Hx. apply (mbyte_of_aview SEGS).
      assert (Hin : inG pe_G x) by (apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; change (Z.of_nat 8) with 8 in Hx; lia).
      destruct (HG x Hin) as [Hi Hns]. destruct (HGR x Hin) as (_ & _ & Her & _). exact (KI x Hi Hns Her). }
  split.
  { unfold p_psopen, pval, pPS, PO_PS in *. destruct HPSO as (P0 & P8). split.
    - eapply vm_frame; [|exact P0]. intros x Hx. apply (mbyte_of_aview SEGS). apply KF. cbn in Hx. lia.
    - eapply vm_frame; [|exact P8]. intros x Hx. apply (mbyte_of_aview SEGS). apply KF. cbn in Hx. lia. }
  split.
  { unfold p_psfresh, p_pspad, pval, pPS, PO_PS in *. destruct HPSF as (P12 & P16 & P20 & P22).
    split; [eapply vm_frame; [|exact P12]; intros x Hx; apply (mbyte_of_aview SEGS); apply KF; cbn in Hx; lia|].
    split; [eapply vm_frame; [|exact P16]; intros x Hx; apply (mbyte_of_aview SEGS); apply KF; cbn in Hx; lia|].
    split; [eapply vm_frame; [|exact P20]; intros x Hx; apply (mbyte_of_aview SEGS); apply KF; cbn in Hx; lia|].
    apply (garr8_frame SEGS _ _ _ _ P22). intros x Hx. apply (mbyte_of_aview SEGS). apply KF. cbn [length] in Hx. lia. }
  { apply (asource_at_frame KS (rdW W3 (ms_mem ms3)) (rdW W2 mem2) h b (p_C cx) 24); [|exact HSRC].
    intros a Ha. apply (mbyte_of_aview SEGS).
    assert (HLC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
    rewrite HLC in Ha. unfold SRC_FILE_BLOCK in Ha.
    destruct Ha as [Ha | [Ha | Ha]].
    - replace a with (h + (a - h)) by lia. apply (KB _ _ _ Hh_in). change (req_size SRC_FILE_BLOCK) with 1304. lia.
    - replace a with (b + (a - b)) by lia. apply (KB _ _ _ Hb_in). lia.
    - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Hns & Her). exact (KI a Hi Hns Her). }
Qed.



(* ---- walk B, the refused arm's free (0x80a84), the return to 0x80a88 and its jump to PP_K12r (0x81124) ---- *)
Definition hss_J : sstate := mkSS 0x350 sr_atoms [] None (mkFacts [] [] []).

Lemma h_B_free : forall POST, pe_from SK B MT KS POST (GI_K12r B MT KS) ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b (regs : bvmap 5 word) mem mdc,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  pe_body cx fp PP_K2 W3 ms3 PSH_ps -> c_n cx < 2 ^ 26 ->
  m_fds md3 = m_fds (c_md cx) -> m_fs md3 = m_fs (c_md cx) ->
  k <= 4 -> acc <= PA_K2r MT cx ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx)]) ->
  asource_none SEGS KS (rdW W3 (ms_mem ms3)) ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem mdc k ->
  m_fds mdc = m_fds md3 -> m_fs mdc = m_fs md3 ->
  getr regs 1 = Z_to_bv 64 (BASE + 848) -> getr regs 2 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) -> getr regs 10 = w64 b ->
  getr regs 20 = w64 (pF cx fp) -> getr regs 23 = w64 (pF cx fp) -> getr regs 25 = w64 (pSH cx fp) ->
  getr regs 27 = w64 SHADOW_OFF ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (seg_rom SEGS)) mdc) (POST cx).
Proof.
  intros POST HK12r cx fp k acc ly3 S3 W3 ms3 md3 b regs mem mdc HB HJ HFR HMO HBODY Hn26 Hfds Hfs
    Hk Hacc HPERM HSN HJc Hfdsc Hfsc Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q20 Q23 Q25 Q27 KR.
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G27 & G3 & G4) & HSAVED & HHDR & HSH &
                       Hlen & HIN).
  pose proof (h_sp cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  destruct (h_base cx HB) as (HROD & HMETA & HG & HGR).
  pose proof HJ as HJ0. destruct HJ as (_ & _ & (memS & HJ & HAG) & _). rewrite !Z.add_0_r in HJ.
  pose proof (h_frame cx fp memS ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR)
    as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof HB as ((_ & _ & Hra4 & Hgp0 & Htp0 & _) & _ & _ & _ & HINP & _ & _ & Hnev0 & Hlive0 & _ & _ & _ & _ & _ & _ & _ &
                    HMOK & Hneed & _ & _ & _ & HTRm & HTRf).
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (HSHr : SB + 512 <= pSH cx fp /\ pSH cx fp + 16 <= SB + 2 ^ 44 /\ pSH cx fp mod 8 = 0).
  { destruct (h_div8_of_mul64 (pF cx fp) HF64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF, SB.
    pose proof (Z.div_lt_upper_bound (pF cx fp + 128) 8 (2 ^ 44) ltac:(dlia1 HFapp) ltac:(lia)).
    pose proof (Z.div_le_lower_bound (pF cx fp) 8 512 ltac:(lia) ltac:(lia)).
    replace ((pF cx fp + 128) / 8) with (pF cx fp / 8 + 16) in H
      by (rewrite <- (Z.div_add (pF cx fp) 16 8) by lia; f_equal; lia).
    split; [lia|]. split; [lia|].
    rewrite E8. replace (2147450880 + 8 * (pF cx fp / 64)) with ((268431360 + pF cx fp / 64) * 8) by lia.
    apply Z_mod_mult. }
  unfold SB in HSHr.
  destruct HJc as (_ & _ & (memS' & HJm & HAGm) & _). rewrite !Z.add_0_r in HJm.
  assert (Esp : spZ regs = c_sp1 cx) by (unfold spZ; rewrite Q2; apply h_w64_unsigned; lia).
  assert (Es0 : s0Z regs = spZ (c_regs cx)) by (unfold s0Z; rewrite Q8; apply h_w64_unsigned; lia).
  assert (Era : raZ regs = BASE + 848).
  { unfold raZ. rewrite Q1, unsigned_lit_small; [reflexivity|]. pose proof pa_base_lo. pose proof pa_B_ok. lia. }
  pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HBok.
  assert (Hb_in : In (b, p_nF cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; left; reflexivity).
  assert (Hb_fr : ~ In (b, p_nF cx) (ablocks B (c_ly cx) (c_S cx))).
  { pose proof (Permutation_NoDup HPERM (h_ablocks_nodup ly3 S3 W3 (ms_mem ms3) md3 HAR3)) as Hnd.
    exact (h_nodup_app_disj _ _ _ _ Hnd (or_introl eq_refl)). }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & _).
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hb_in Hfin) as Db.
  rewrite EF in Db. change (fs_frame_bytes PE_CID) with 128 in Db.
  assert (Hmo : mo_ok MT S3 (mo_free MT)).
  { pose proof (PA_K12_need MT MTL cx) as HN. pose proof (PA_refused_le MT MTL cx) as HR.
    apply (mo_ok_le MT MTL S3 _ (c_T cx - acc)); [|lia].
    apply (mo_ok_step MT MTL (c_S cx) S3 acc (c_T cx - acc)); [|exact HMO].
    replace (acc + (c_T cx - acc)) with (c_T cx) by lia. exact HMOK. }
  eapply SRr_bind.
  { eapply (afree04_sub_fs SK SEGS B LAWS pa_segs_low MT AF W3 regs mem LLVMF_STK (spZ (c_regs cx)) [sink_token]
      (c_ly cx) (c_S cx) (c_W cx) memS' (c_md cx) [(PE_CID, fp)] ly3 S3 mdc k b (p_nF cx) (c_sp1 cx - spZ (c_regs cx))
      (Z_to_bv 64 (BASE + 848)) (pch cx) HJm Hb_in Q10).
    - rewrite Esp. lia.
    - replace (c_sp1 cx - spZ (c_regs cx)) with ((c_sp1 cx / 16 - spZ (c_regs cx) / 16) * 16)
        by (pose proof (h_mod32_8 _ Hsp1_32) as [M16 _]; pose proof (Z_div_mod_eq_full (c_sp1 cx) 16);
            pose proof (Z_div_mod_eq_full (spZ (c_regs cx)) 16); lia).
      apply Z.mod_mul. lia.
    - lia.
    - unfold ASTACK, LLVMF_STK. lia.
    - rewrite Q3. exact Hgp0.
    - rewrite Q4. exact Htp0.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold EV_LIB in *. lia.
    - apply (achain_chain_pre ly3 (aview SEGS (w_H W3) mem) (c_sp1 cx) (spZ (c_regs cx)) (pch cx) regs).
      + apply (h_achain cx memS' ly3 S3 W3 mem _ [(PE_CID, fp)] k (c_sp1 cx) HB HJm HAGm).
        * apply (h_rdword_keep (w_H W3) (w_H W3) (ms_mem ms3) mem); [|exact (proj1 HSAVED)].
          intros i Hi. apply KR; lia.
        * pose proof (proj2 HSAVED 0 ltac:(lia)) as HS0. rewrite Z.mul_0_r, Z.sub_0_r in HS0.
          apply (h_rdword_keep (w_H W3) (w_H W3) (ms_mem ms3) mem); [|exact HS0].
          intros i Hi. apply KR; lia.
        * lia.
      + rewrite Esp. lia.
      + exact Es0.
      + rewrite Era. lia.
    - apply HTRf. rewrite Era. replace (BASE + 848 - BASE) with 848 by lia. cbn. left. reflexivity.
    - intros Hin. exfalso. exact (Hb_fr Hin).
    - exact Hmo. }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HPR & (l1 & l2 & Eb3 & Eb2) & Hfr2 & HK & MLE &
                                Hfd2 & Hfs2).
  subst c2. destruct HK as (K1 & K2 & K3 & K4 & _ & _).
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in K1 by lia.
  pose proof HJ2 as (HAR2 & Hly2 & _).
  (* what the call kept: the caller's other blocks, the frame and its shadow, the stack above its window, the image *)
  assert (KB : forall p m i, In (p, m) (ablocks B ly3 S3) -> (p, m) <> (b, p_nF cx) -> 0 <= i < req_size m ->
     aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W3) (ms_mem ms3) (p + i)).
  { intros p m i Hin Hne Hi.
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin Hb_in Hne) as D.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
    rewrite (K2 p m i Hin Hi); [apply KR; lia|]. cbn beta. dlia1 D. }
  assert (KF : forall a, (pF cx fp <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite (K4 PE_CID fp a Hfin).
    - apply KR. lia.
    - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr; cbn [frame_rng fst snd];
        [rewrite EF; change (fs_frame_bytes PE_CID) with 128; lia|].
      replace (shadow_addr (frame_addr ly3 PE_CID fp)) with (pSH cx fp) by (rewrite EF, ESH; unfold shadow_addr; reflexivity).
      change (fs_frame_bytes PE_CID / 8) with 16. lia.
    - cbn beta. destruct Ha as [Ha | Ha]; [dlia1 Db | dlia1 Hbapp]. }
  assert (KH : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite K1; [apply KR; lia | lia | lia]. }
  assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Hi Hns Her. rewrite (K3 a Hi Hns Her). apply KR. exact (h_img_range a Hi). }
  (* the jump 0x80a88 -> PP_K12r *)
  remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
  assert (HS2 : st_ok_pi SEGS VAL E2 hss_J (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 848)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold hss_J. apply pa_entry_st_ok_full.
    - rewrite HE2. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - apply pairwise_disjoint_of_extents. cbn. exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK2 : sh_ok SEGS (SLit SB) [] E2 (rdW W2 mem2)) by constructor.
  assert (HJx : ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly2 S2 W2 mem2 md2 (k + 1)).
  { eapply ajournal_gx_pack; [unfold LLVMF_STK; lia | lia | | exact HAGm | intros a Ha _; lia].
    rewrite (Z.add_0_r LLVMF_STK), (Z.add_0_r (spZ (c_regs cx))). exact HJ2. }
  pose (RUNTOX := paj_run_to_x B LAWS pe_G HG 0 []).
  paj_run_to_tok RUNTOX HS2 HJx SHOK2 hBspan0 PP_K12r.
  { apply awr_ok_x_of0. apply awr_ok_nil. }
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E2 [] (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr);
      [intros bb wlo whi x Hin _; vm_compute in Hin; destruct Hin | exact Ha | intros []]. }
  prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4. prreg HS2 (8%bv : bv 5) T8.
  prreg HS2 (9%bv : bv 5) T9. prreg HS2 (20%bv : bv 5) T20. prreg HS2 (23%bv : bv 5) T23. prreg HS2 (25%bv : bv 5) T25.
  prreg HS2 (27%bv : bv 5) T27.
  assert (ER : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E2 q = getr regs2 r)
    by (intros q r Hq; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hq).
  rewrite (ER 2%nat 2%bv eq_refl), (h_pres _ _ _ HPR) in T2 by acs.
  rewrite (ER 3%nat 3%bv eq_refl), (h_pres _ _ _ HPR) in T3 by acs.
  rewrite (ER 4%nat 4%bv eq_refl), (h_pres _ _ _ HPR) in T4 by acs.
  rewrite (ER 8%nat 8%bv eq_refl), (h_pres _ _ _ HPR) in T8 by acs.
  rewrite (ER 9%nat 9%bv eq_refl), (h_pres _ _ _ HPR) in T9 by acs.
  rewrite (ER 20%nat 20%bv eq_refl), (h_pres _ _ _ HPR) in T20 by acs.
  rewrite (ER 23%nat 23%bv eq_refl), (h_pres _ _ _ HPR) in T23 by acs.
  rewrite (ER 25%nat 25%bv eq_refl), (h_pres _ _ _ HPR) in T25 by acs.
  rewrite (ER 27%nat 27%bv eq_refl), (h_pres _ _ _ HPR) in T27 by acs.
  pmkst HS2.
  apply (HK12r cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 (mkst (ms_regs ms) (Z_to_bv 64 (BASE + 2540)) (ms_mem ms) (seg_rom SEGS))
           _ HB HJx).
  { rewrite Hfr2. exact HFR. }
  { exact (mo_le_trans MT MTL _ _ _ _ _ HMO MLE). }
  split.
  { exists PSH_ps. split; [right; reflexivity|].
    unfold p_cut. split.
    2:{ split; [unfold EV_LIB; lia|]. split; [pose proof (PA_refused_le MT MTL cx); lia|].
        split.
        { rewrite Eb2. rewrite Eb3 in HPERM.
          apply (Permutation_app_inv l1 l2 (ablocks B (c_ly cx) (c_S cx)) [] (b, p_nF cx)). exact HPERM. }
        split; [rewrite (proj1 (wvb_fds_fs _ _ _)), Hfd2, Hfdsc; exact Hfds
               | rewrite (proj2 (wvb_fds_fs _ _ _)), Hfs2, Hfsc; exact Hfs]. }
    unfold pe_body, pregs, psaved, pheader, pshadow.
    cbn [ms_mem ms_regs ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { split; [rewrite T2; exact Q2|]. split; [rewrite T8; exact Q8|]. split; [rewrite T9; exact Q9|].
      split; [rewrite T27; exact Q27|]. split; [rewrite T3; exact Q3 | rewrite T4; exact Q4]. }
    split.
    { split.
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) (ms_mem ms)); [|exact (proj1 HSAVED)].
        intros i Hi. rewrite KR2 by lia. apply KH. lia.
      - intros j Hj. apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) (ms_mem ms)); [|exact (proj2 HSAVED j Hj)].
        intros i Hi. rewrite KR2 by lia. apply KH. lia. }
    split.
    { destruct HHDR as (HH0 & HH8 & HH16 & HH120). unfold PE_FLAGPTR in HH120 |- *.
      split; [|split; [|split]];
        (apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) (ms_mem ms)); [intros i Hi; rewrite KR2 by lia; apply KF;
           lia|]); assumption. }
    split; [intros i Hi; change (length PSH_ps) with 16%nat in Hi; rewrite KR2 by lia; rewrite KF; [exact (HSH i Hi) | lia]|].
    split; [reflexivity|].
    { apply (garr8_frame SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms)) _ _ HIN). intros a Ha. rewrite length_map in Ha.
      apply (mbyte_of_aview SEGS).
      destruct HINP as [(Hn0 & _) | (Hn & Hinc)]; [unfold c_n in Hn0; lia|].
      assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hinc).
      assert (Hne : (c_p cx, c_n cx) <> (b, p_nF cx)) by (intros E'; apply Hb_fr; rewrite <- E'; exact Hinc).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreqp].
      unfold c_n in *. rewrite KR2 by lia. replace a with (c_p cx + (a - c_p cx)) by lia. apply (KB _ _ _ Hin3 Hne). lia. } }
  cbn [ms_mem ms_regs mkst].
  split; [exact Hn26|]. split; [rewrite T20; exact Q20|]. split; [rewrite T23; exact Q23|]. split; [rewrite T25; exact Q25|].
  apply (asource_none_frame KS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms))); [|exact HSN].
  intros a Ha. apply (mbyte_of_aview SEGS). destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Hns & Her).
  rewrite KR2 by exact (h_img_range a Hi). exact (KI a Hi Hns Her).
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* Walk B: PP_K2 (0x809a0) -> the harness's own check of the open's verdict (0x809a0..0x80a70) ->   *)
(*   accepted: malloc 0x80ab8 -> PP_K3;  refused: free 0x80a84 -> PP_K12r                          *)
(* ---------------------------------------------------------------------------------------------- *)
(* 0x809a0 a3 := g_file_len (through slot 64, hi 8 + 0x618); bltu a3,4 0x809b0 skips the magic; 0x809b4..0x80a2c four
   shadow-checked byte loads of the copy b (s3) form the magic a4; bltu a3,24 0x80a30; the magic tests 0x80a3c /
   0x80a58..0x80a70 and the consistency of the open's verdict a0 with them (every mismatch jumps to PP_abort); 0x80a74
   beqz a0: refused (ps.f = 0 checked 0x80a7c, free(b) 0x80a84, j PP_K12r) or accepted (ps.swapped checked 0x80aa0,
   cap := 8 d (0x80aa8), malloc(cap ? cap : 1) 0x80ab8). *)
Definition hR_slotsB : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 96 0 0
    [YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff (A_HI 8) 0)); YP09.mkChunk 88 (CVal 8 (SOff 23 32))].
Definition hR_glen : YP09.region := YP09.mkRegion (Some (A_HI 8)) PE_GLEN_LO PE_GLEN_LO8 PE_GLEN_LO PE_GLEN_LO [YP09.mkChunk PE_GLEN_LO (CVal 8 (SOff 33 0))].
Definition hR_psacc : YP09.region := YP09.mkRegion (Some 23%nat) 32 56 32 32 [YP09.mkChunk 40 (CVal 4 (SOff 38 0))].
Definition hR_psref : YP09.region := YP09.mkRegion (Some 23%nat) 32 56 32 32 [YP09.mkChunk 32 (CVal 8 (SLit 0))].
Definition hR_copy : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 4 0 0
    [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SOff 35 0)); YP09.mkChunk 2 (CVal 1 (SOff 36 0));
     YP09.mkChunk 3 (CVal 1 (SOff 37 0))].
Definition hfacts_B (big acc : bool) : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF 4096 (2 ^ 47 - 16) 4); (23%nat, mkAF 4096 (2 ^ 47) 6);
           (27%nat, mkAF SB SB 0);
           (33%nat, if acc then mkAF 24 (2 ^ 26 - 1) 0 else if big then mkAF 4 (2 ^ 26 - 1) 0 else mkAF 0 3 0);
           (10%nat, if acc then mkAF 0 0 0 else mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0);
           (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0);
           (38%nat, mkAF 0 1 0); (32%nat, mkAF 0 255 0)] [] [].
Definition hss_B (big acc : bool) : sstate :=
  mkSS PP_K2 sr_atoms
    (hR_slotsB :: hR_glen :: (if acc then hR_psacc else hR_psref) :: (if big then [hR_copy] else [])) None (hfacts_B big acc).
Definition hSH_B (big : bool) : list shent := if big then [mkSHE 19 0 4] else [].
Definition hBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition hBx : sv := SOff 27 0.

Lemma h_shent_B : forall Ex (m : word -> option byte) big p,
  U Ex hBx = SHADOW_OFF -> U Ex (SOff 19 0) = p ->
  (big = true -> (4096 <= p /\ (p + 4 <= kLowShadowBeg \/ kHighMemBeg <= p)) /\
     range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF p 4) ->
  sh_ok SEGS hBx (hSH_B big) Ex m.
Proof.
  intros Ex m big p HB Hq Hz. destruct big; [|constructor].
  destruct (Hz eq_refl) as [Hz1 HR].
  unfold sh_ok, hSH_B. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq. split.
  - rewrite Z.add_0_r. exact HR.
  - intros a Ha. cbn in Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Hypothesis HGLEN : VAL (A_HI 8) + PE_GLEN_LO = VAL (A_OBJ 4).

Theorem pe_B : forall POST, pe_from SK B MT KS POST (GI_K3 B MT KS) -> pe_from SK B MT KS POST (GI_K12r B MT KS) ->
  pe_from SK B MT KS POST (GI_K2 B MT KS).
Proof.
  intros POST HK3 HK12r cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  destruct HI as (b & HBODY & Hn26 & Hfds & Hfs & R19 & R20 & R23 & R25 & SD & SGLEN & SPSP & HGL & HCOPY & HARM).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G27 & G3 & G4) & HSAVED & HHDR & HSH &
                       Hlen & HIN).
  pose proof (h_sp cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  destruct (h_base cx HB) as (HROD & HMETA & HG & HGR).
  pose proof HJ as HJ0. destruct HJ as (_ & _ & (memS & HJ & HAG) & _). rewrite !Z.add_0_r in HJ.
  pose proof (h_frame cx fp memS ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR)
    as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof (p_d_range cx) as Hd.
  assert (Hb_in : In (b, p_nF cx) (ablocks B ly3 S3)).
  { destruct HARM as [(_ & _ & _ & _ & h & HP & _) | (_ & _ & _ & _ & HP & _)];
      (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; left; reflexivity). }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & _).
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hb_in Hfin) as Db.
  rewrite EF in Db. change (fs_frame_bytes PE_CID) with 128 in Db.
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR3 Hb_in) as Hbimg.
  assert (HSHr : SB + 512 <= pSH cx fp /\ pSH cx fp + 16 <= SB + 2 ^ 44 /\ pSH cx fp mod 8 = 0).
  { destruct (h_div8_of_mul64 (pF cx fp) HF64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF, SB.
    pose proof (Z.div_lt_upper_bound (pF cx fp + 128) 8 (2 ^ 44) ltac:(dlia1 HFapp) ltac:(lia)).
    pose proof (Z.div_le_lower_bound (pF cx fp) 8 512 ltac:(lia) ltac:(lia)).
    replace ((pF cx fp + 128) / 8) with (pF cx fp / 8 + 16) in H
      by (rewrite <- (Z.div_add (pF cx fp) 16 8) by lia; f_equal; lia).
    split; [lia|]. split; [lia|].
    rewrite E8. replace (2147450880 + 8 * (pF cx fp / 64)) with ((268431360 + pF cx fp / 64) * 8) by lia.
    apply Z_mod_mult. }
  unfold SB in HSHr.
  set (bt := fun i => nth i (p_C cx) 0).
  remember (Eimg (Ereg (ms_regs ms3) (map (Z_to_bv 64) [p_d cx; p_nF cx; bt 0%nat; bt 1%nat; bt 2%nat; bt 3%nat; p_swz cx])))
    as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
    by (intros q r Hq; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (EX : forall i, (i < 7)%nat -> ew E (32 + i) =
      nth i (map (Z_to_bv 64) [p_d cx; p_nF cx; bt 0%nat; bt 1%nat; bt 2%nat; bt 3%nat; p_swz cx]) (Z_to_bv 64 0)).
  { intros i Hi. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  assert (Hbt : forall i, 0 <= bt i < 256).
  { intros i. unfold bt, p_C. destruct (Nat.lt_ge_cases i (length (p_F cx))) as [Hi | Hi].
    - rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hi).
      rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth i (p_F cx) (Z_to_bv 8 0))) as R. unfold bv_modulus in R. exact R.
    - rewrite nth_overflow by (rewrite length_map; exact Hi). lia. }
  assert (Hswz : p_swz cx = 0 \/ p_swz cx = 1) by (unfold p_swz, PST.pcap_sw; destruct (_ =? _); [right | left]; reflexivity).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply h_w64_unsigned; lia).
  assert (U19 : bv_unsigned (ew E 19) = b) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply h_w64_unsigned; lia).
  assert (U23 : bv_unsigned (ew E 23) = pF cx fp) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply h_w64_unsigned; lia).
  assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite (EE 27%nat 27%bv eq_refl), G27; apply h_w64_unsigned; unfold SHADOW_OFF; lia).
  assert (UX : forall i v, (i < 7)%nat -> nth i [p_d cx; p_nF cx; bt 0%nat; bt 1%nat; bt 2%nat; bt 3%nat; p_swz cx] 0 = v ->
      0 <= v < 2 ^ 64 -> bv_unsigned (ew E (32 + i)) = v).
  { intros i v Hi Hv Hr. rewrite (EX i Hi). rewrite map_nth. rewrite Hv. apply h_w64_unsigned. exact Hr. }
  pose proof (pa_obj_img 4 ltac:(lia)) as Hobj4. pose proof (pa_val_range (A_HI 8)) as Hhi8r.
  unfold pcap_img_end, YImgTop.IMG_TOP in Hobj4.
  assert (UHI : bv_unsigned (ew E (A_HI 8)) = VAL (A_HI 8)).
  { rewrite (img_env_atomP E (A_HI 8) HEI) by (unfold A_HI, A_TEXT, A_LIM; lia). apply h_w64_unsigned. exact Hhi8r. }
  destruct HGL as (HGL2 & HGL4). unfold pval in HGL2, HGL4.
  (* the symbolic state at 0x809a0, for each arm and each size class of the copy *)
  assert (HSgen : forall bg ac,
     (ac = true -> 24 <= p_nF cx /\ getr (ms_regs ms3) 10 = w64 0 /\
                    val_mem SEGS (rdW W3 (ms_mem ms3)) (pF cx fp + 32 + 8) 4 (p_swz cx)) ->
     (ac = false -> getr (ms_regs ms3) 10 = w64 (-1) /\ val_mem SEGS (rdW W3 (ms_mem ms3)) (pF cx fp + 32) 8 0 /\
                     (bg = true -> 4 <= p_nF cx) /\ (bg = false -> p_nF cx < 4)) ->
     (ac = true -> bg = true) ->
     st_ok_pi SEGS VAL E (hss_B bg ac) (restrict (w_H W3) ms3) /\ sh_ok SEGS hBx (hSH_B bg) E (rdW W3 (ms_mem ms3))).
  { intros bg ac HA HRf HAB.
    assert (Hb4 : bg = true -> 4 <= p_nF cx).
    { intros ->. destruct ac; [lia | exact (proj1 (proj2 (proj2 (HRf eq_refl))) eq_refl)]. }
    assert (U10 : ac = true -> bv_unsigned (ew E 10) = 0)
      by (intros Ha; rewrite (EE 10%nat 10%bv eq_refl), (proj1 (proj2 (HA Ha))); apply h_w64_unsigned; lia).
    assert (U10r : ac = false -> bv_unsigned (ew E 10) = 2 ^ 64 - 1)
      by (intros Ha; rewrite (EE 10%nat 10%bv eq_refl), (proj1 (HRf Ha)); unfold w64; rewrite Z_to_bv_unsigned; reflexivity).
    split.
    2:{ apply (h_shent_B E _ bg b).
        - unfold hBx. apply (U_atom E 27 SHADOW_OFF); [rewrite (EE 27%nat 27%bv eq_refl), G27; reflexivity | unfold SHADOW_OFF; lia].
        - apply (U_atom E 19 b); [rewrite (EE 19%nat 19%bv eq_refl), R19; reflexivity | lia].
        - intros Hbig. specialize (Hb4 Hbig). split; [unfold kLowShadowBeg, kHighMemBeg; dlia1 Hbapp|].
          destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as [HBS _].
          apply (block_shadow_range _ _ b (req_size (p_nF cx))); [exact HBS | lia | lia]. }
    rewrite (h_restrict_body cx fp PP_K2 W3 ms3 PSH_ps HBODY). unfold hss_B.
    apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - destruct bg, ac; vm_compute; reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|]]].
      + unfold region_ok, hR_slotsB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        * apply (h_slot_chunk_ok E (w_H W3) (ms_mem ms3) (c_sp1 cx) 32 (SOff 32 0) (p_d cx)); [exact SD | | lia].
          rewrite h_denot_off0. exact (EX 0%nat ltac:(lia)).
        * apply (h_slot_chunk_ok E (w_H W3) (ms_mem ms3) (c_sp1 cx) 64 (SOff (A_HI 8) 0) (VAL (A_HI 8))); [exact SGLEN | |].
          { rewrite h_denot_off0. apply (img_env_atomP E (A_HI 8) HEI). unfold A_HI, A_TEXT, A_LIM. lia. }
          { apply pa_val_range. }
        * apply (h_slot_chunk_ok E (w_H W3) (ms_mem ms3) (c_sp1 cx) 88 (SOff 23 32) (pF cx fp + 32)); [exact SPSP | | lia].
          apply (h_denot_off E 23 (pF cx fp) 32); [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia].
      + unfold region_ok, hR_glen. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite UHI. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E (rdW W3 (ms_mem ms3)) (VAL (A_HI 8)) PE_GLEN_LO 8%N (SOff 33 0) (p_nF cx)).
        * rewrite h_denot_off0. exact (EX 1%nat ltac:(lia)).
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * change (N.to_nat 8) with 8%nat. rewrite HGLEN. exact HGL4.
      + destruct ac.
        * destruct (HA eq_refl) as (_ & _ & HSW).
          unfold region_ok, hR_psacc. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS E (rdW W3 (ms_mem ms3)) (pF cx fp) 40 4%N (SOff 38 0) (p_swz cx)).
          -- rewrite h_denot_off0. exact (EX 6%nat ltac:(lia)).
          -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
          -- cbn. lia.
          -- change (N.to_nat 4) with 4%nat. replace (pF cx fp + 40) with (pF cx fp + 32 + 8) by lia. exact HSW.
        * destruct (HRf eq_refl) as (_ & HPN & _).
          unfold region_ok, hR_psref. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS E (rdW W3 (ms_mem ms3)) (pF cx fp) 32 8%N (SLit 0) 0).
          -- reflexivity.
          -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
          -- cbn. lia.
          -- change (N.to_nat 8) with 8%nat. exact HPN.
      + destruct bg; [|apply Forall_nil]. specialize (Hb4 eq_refl).
        apply Forall_cons; [|apply Forall_nil].
        unfold region_ok, hR_copy. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        unfold p_copy in HCOPY.
        assert (HCB : forall i : nat, (i < 4)%nat ->
            YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) b (YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (34 + i) 0)))).
        { intros i Hi. destruct (HCOPY i) as [Hv Hr].
          { unfold p_C. rewrite length_map. unfold p_nF in Hb4. lia. }
          apply (chunk_ok_val SEGS E (rdW W3 (ms_mem ms3)) b (Z.of_nat i) 1%N (SOff (34 + i) 0) (bt i)).
          - rewrite h_denot_off0. replace (34 + i)%nat with (32 + (2 + i))%nat by lia. rewrite (EX (2 + i)%nat ltac:(lia)).
            do 4 (destruct i as [|i]; [reflexivity|]). lia.
          - change (2 ^ (8 * Z.of_N 1)) with 256. exact (Hbt i).
          - cbn. lia.
          - exact Hv. }
        apply Forall_cons; [exact (HCB 0%nat ltac:(lia))|]. apply Forall_cons; [exact (HCB 1%nat ltac:(lia))|].
        apply Forall_cons; [exact (HCB 2%nat ltac:(lia))|]. apply Forall_cons; [exact (HCB 3%nat ltac:(lia))|].
        apply Forall_nil.
    - apply pairwise_disjoint_of_extents.
      destruct bg, ac; unfold hR_slotsB, hR_glen, hR_psacc, hR_psref, hR_copy, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U9, ?UHI, ?U23, ?U19; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        repeat split; first [lia | dlia1 HFimg | dlia1 Hbimg | dlia1 Db].
    - assert (U32 : bv_unsigned (ew E 32) = p_d cx) by exact (UX 0%nat (p_d cx) ltac:(lia) eq_refl ltac:(lia)).
      assert (U33 : bv_unsigned (ew E 33) = p_nF cx) by exact (UX 1%nat (p_nF cx) ltac:(lia) eq_refl ltac:(lia)).
      assert (U34 : bv_unsigned (ew E 34) = bt 0%nat) by (pose proof (Hbt 0%nat); exact (UX 2%nat (bt 0%nat) ltac:(lia) eq_refl ltac:(lia))).
      assert (U35 : bv_unsigned (ew E 35) = bt 1%nat) by (pose proof (Hbt 1%nat); exact (UX 3%nat (bt 1%nat) ltac:(lia) eq_refl ltac:(lia))).
      assert (U36 : bv_unsigned (ew E 36) = bt 2%nat) by (pose proof (Hbt 2%nat); exact (UX 4%nat (bt 2%nat) ltac:(lia) eq_refl ltac:(lia))).
      assert (U37 : bv_unsigned (ew E 37) = bt 3%nat) by (pose proof (Hbt 3%nat); exact (UX 5%nat (bt 3%nat) ltac:(lia) eq_refl ltac:(lia))).
      assert (U38 : bv_unsigned (ew E 38) = p_swz cx) by exact (UX 6%nat (p_swz cx) ltac:(lia) eq_refl ltac:(lia)).
      pose proof (Hbt 0%nat). pose proof (Hbt 1%nat). pose proof (Hbt 2%nat). pose proof (Hbt 3%nat).
      split; [|split; exact I].
      destruct bg, ac; cbn [hfacts_B f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
        rewrite U9, U19, U23, U27, U33, U34, U35, U36, U37, U38, U32;
        rewrite ?(U10 eq_refl), ?(U10r eq_refl); unfold SB, SHADOW_OFF;
        repeat match goal with |- _ /\ _ => split end;
        first [ lia | (change (2 ^ 5) with 32; exact Hsp1_32) | (change (2 ^ 4) with 16; exact Hb16)
              | (change (2 ^ 6) with 64; exact HF64) | (change (2 ^ 0) with 1; apply Z.mod_1_r)
              | (destruct (HA eq_refl) as (H24 & _); lia) | (destruct (HRf eq_refl) as (_ & _ & H4 & H4'); first [specialize (H4 eq_refl) | specialize (H4' eq_refl)]; lia) ]. }
  pose (RUNX := paj_run_x B LAWS pe_G HG 0 []).
  pose (BRX := paj_branch (PI := PI)).
  pose proof HJ0 as HJ3. clear HJ. rename HJ0 into HJ.
  assert (EB : forall (Ex : env), (forall n, (n < 512)%nat -> ew Ex n = ew E n) ->
     U Ex h_magic_sv = PST.pcap_magic (p_F cx) + h_magic_X cx).
  { intros Ex HEx. apply h_magic_U_cx; rewrite HEx by lia;
      [exact (EX 2%nat ltac:(lia)) | exact (EX 3%nat ltac:(lia)) | exact (EX 4%nat ltac:(lia)) | exact (EX 5%nat ltac:(lia))]. }
  destruct HARM as [(Hgood & R10 & Hk2 & Hacc2 & h & HPERM & HPSO & HPSF & HSRC) |
                    (Hgood & R10 & Hk2 & Hacc2 & HPERM & HPSN & HSN)].
  - (* accepted: a0 = 0, the file is good *)
    assert (H24 : 24 <= p_nF cx).
    { unfold p_good, PST.pcap_good in Hgood. apply andb_prop in Hgood as [H24 _]. apply Z.leb_le in H24. exact H24. }
    destruct HPSO as (HPSO1 & HPSO2). unfold pval, pPS, PO_PS in HPSO1, HPSO2.
    destruct (HSgen true true (fun _ => conj H24 (conj R10 HPSO2)) ltac:(discriminate) (fun _ => eq_refl)) as [HS SHOK].
    paj_run_tok RUNX HS HJ SHOK hBspan.
    { apply awr_ok_x_of0.
      lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end.
      apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx)); [reflexivity | exact U9 | intros a Ha; cbn in Ha; lia |].
      apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (A_HI 8) (VAL (A_HI 8))); [reflexivity | exact UHI | intros a Ha; cbn in Ha; lia |].
      apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (pF cx fp)); [reflexivity | exact U23 | intros a Ha; cbn in Ha; lia |].
      apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat b); [reflexivity | exact U19 | intros a Ha; cbn in Ha; lia |].
      apply awr_ok_nil. }
    assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply (kept_of_frame (segs := SEGS) E (ss_mem (hss_B true true)) (w_H W3) (ms_mem ms3) (ms_mem ms)
        (fun _ => False) HFr); [|exact Ha | intros []].
      intros bb wlo whi x Hin Hx. vm_compute in Hin.
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia |]). destruct Hin. }
    clear HF HFr HG0.
    psrr_branch_tok RUNX BRX HS SHOK hBspan.
    + (* 0x80a3c bne a4, A1B2C3D4 taken: the magic is the swapped one *)
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
        assert (EMa : U Ex h_magic_sv = PST.pcap_magic (p_F cx) + h_magic_X cx)
          by (apply EB; intros n Hn; rewrite !ew_ewset_other by lia; reflexivity);
        unfold h_magic_sv in EMa;
        rewrite branch_ne_U, EMa, (U_lit Ex 18446744072127431636 ltac:(lia)) in Hc end.
      apply negb_true_iff, Z.eqb_neq in Hc.
      destruct (h_good_cases cx Hgood) as (H24g & [(HMg & HSw) | (HMg & HSw)]);
        [exfalso; exact (Hc (proj2 (proj1 (h_U_K cx)) HMg))|].
      assert (EUK2 : PST.pcap_magic (p_F cx) + h_magic_X cx = h_K2)
        by (exact (proj2 (proj2 (h_U_K cx)) HMg)).
      clear Hc.
      paj_run_tok RUNX HS HJ SHOK hBspan.
      { hawr0. }
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
        assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
          by hkr HFr KR1 end.
      clear HF HFr HG0 KR1.
      psrr_branch_tok RUNX BRX HS SHOK hBspan.
      * (* 0x80a70 bne a0, a2 to PP_abort: a2 = 0 = a0, so not taken *)
        exfalso.
        lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
          assert (EMb : U Ex h_magic_sv = PST.pcap_magic (p_F cx) + h_magic_X cx)
            by (apply EB; intros n Hn; rewrite !ew_ewset_other by lia; reflexivity);
          assert (X10 : ew Ex 10 = Z_to_bv 64 0)
            by (rewrite !ew_ewset_other by lia; rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity);
          pose proof (h_a2_U Ex _ EMb) as HA2; unfold h_seqz_sv, h_magic_sv, h_K2 in HA2;
          rewrite branch_ne_U, (U_atom Ex 10 0 X10 ltac:(lia)), HA2 in Hc end.
        rewrite EUK2, Z.eqb_refl in Hc. cbn in Hc. discriminate Hc.
      * paj_run_tok RUNX HS HJ SHOK hBspan.
        { hawr0. }
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
          assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
            by hkr HFr KR2 end.
        clear HF HFr HG0 KR2 Hc.
        psrr_branch_tok RUNX BRX HS SHOK hBspan.
        -- (* 0x80a74 beqz a0: taken, the open accepted *)
           paj_run_tok RUNX HS HJ SHOK hBspan.
           { hawr0. }
           lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
             assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
               by hkr HFr KR3 end.
           clear HF HFr HG0 KR3 Hc.
           psrr_branch_tok RUNX BRX HS SHOK hBspan.
           ++ (* 0x80aa0 bne ps.swapped, seqz to PP_abort: both are 1 here *)
              exfalso.
              lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
                assert (EMc : U Ex h_magic_sv = PST.pcap_magic (p_F cx) + h_magic_X cx)
                  by (apply EB; intros n Hn; rewrite !ew_ewset_other by lia; reflexivity);
                assert (X38 : ew Ex 38 = Z_to_bv 64 (p_swz cx))
                  by (rewrite !ew_ewset_other by lia; exact (EX 6%nat ltac:(lia)));
                pose proof (h_seqz_gen Ex (SAlu ALU_ADD h_magic_sv (SLit 0)) _ (h_mv_U Ex _ EMc)) as HSZ;
                unfold h_magic_sv, h_K2 in HSZ;
                rewrite branch_ne_U, (U_atom Ex 38 (p_swz cx) X38 ltac:(rewrite HSw; lia)), HSZ in Hc end.
              rewrite EUK2, Z.eqb_refl, HSw in Hc. cbn in Hc. discriminate Hc.
           ++ (* not taken: on to the record buffer's malloc *)
              paj_run_tok RUNX HS HJ SHOK hBspan.
              { hawr0. }
              lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
                assert (KR5 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                  by hkr HFr KR4 end.
              clear HF HFr HG0 KR4 Hc.
              psrr_branch_tok RUNX BRX HS SHOK hBspan.
              ** (* 0x80ab0 bnez d: the capacity is 8 d *)
                 paj_run_tok RUNX HS HJ SHOK hBspan.
                 { hawr0. }
                 lazymatch type of HS with
                 | st_ok_pi _ _ _ _ (restrict _ ?msn) =>
                   assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                     by hkr HFr KR5
                 | st_ok _ _ _ (restrict _ ?msn) =>
                   assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                     by hkr HFr KR5 end.
                 lazymatch type of HS with
                 | st_ok_pi _ _ ?Ex _ _ =>
                   assert (X32 : ew Ex 32 = Z_to_bv 64 (p_d cx))
                     by (rewrite !ew_ewset_other by lia; exact (EX 0%nat ltac:(lia)));
                   rewrite branch_ne_U, (U_atom Ex 32 (p_d cx) X32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc
                 | st_ok _ ?Ex _ _ =>
                   assert (X32 : ew Ex 32 = Z_to_bv 64 (p_d cx))
                     by (rewrite !ew_ewset_other by lia; exact (EX 0%nat ltac:(lia)));
                   rewrite branch_ne_U, (U_atom Ex 32 (p_d cx) X32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc end.
                 apply negb_true_iff, Z.eqb_neq in Hc.
                 clear HF HFr HG0 KR5.
                 prreg HS (1%bv : bv 5) Z1; prreg HS (2%bv : bv 5) Z2; prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4;
                 prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9; prreg HS (10%bv : bv 5) Z10; prreg HS (19%bv : bv 5) Z19;
                 prreg HS (20%bv : bv 5) Z20; prreg HS (21%bv : bv 5) Z21; prreg HS (23%bv : bv 5) Z23;
                 prreg HS (25%bv : bv 5) Z25; prreg HS (27%bv : bv 5) Z27;
                 try rewrite !ew_ewset_other in Z2, Z3, Z4, Z8, Z9, Z19, Z20, Z23, Z25, Z27 by lia;
                 rewrite (EE 2%nat 2%bv eq_refl), G2 in Z2; rewrite (EE 3%nat 3%bv eq_refl), G3 in Z3;
                 rewrite (EE 4%nat 4%bv eq_refl), G4 in Z4; rewrite (EE 8%nat 8%bv eq_refl), G8 in Z8;
                 rewrite (EE 9%nat 9%bv eq_refl), G9 in Z9; rewrite (EE 19%nat 19%bv eq_refl), R19 in Z19;
                 rewrite (EE 20%nat 20%bv eq_refl), R20 in Z20; rewrite (EE 23%nat 23%bv eq_refl), R23 in Z23;
                 rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25; rewrite (EE 27%nat 27%bv eq_refl), G27 in Z27.
                 assert (X32' : ew E 32 = Z_to_bv 64 (p_d cx)) by exact (EX 0%nat ltac:(lia)).
                 rewrite X32', (h_sll3 (p_d cx) ltac:(lia)) in Z10, Z21.
                 assert (Z10' : getr (ms_regs _) 10 = w64 (p_bn cx))
                   by (rewrite Z10; unfold p_bn, p_cap; rewrite Z.max_l by lia; reflexivity).
                 assert (Z21' : getr (ms_regs _) 21 = w64 (p_cap cx)) by (rewrite Z21; unfold p_cap; reflexivity).
                 pmkst HS. rewrite (pal_malloc B TL).
                 refine (h_B_malloc POST HK3 cx fp k acc ly3 S3 W3 ms3 md3 b h _ _ _ HB HJ3 HFR HMO HBODY Hn26 Hfds Hfs
                   SD SGLEN SPSP (conj HGL2 HGL4) Hgood Hk2 Hacc2 HPERM (conj HPSO1 HPSO2) HPSF HSRC HJ
                   (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))
                   Z1 Z2 Z3 Z4 Z8 Z9 Z10' Z19 Z20 Z21' Z23 Z25 Z27 KR6).
              ** (* d = 0: the harness asks for one byte *)
                 paj_run_tok RUNX HS HJ SHOK hBspan.
                 { hawr0. }
                 lazymatch type of HS with
                 | st_ok_pi _ _ _ _ (restrict _ ?msn) =>
                   assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                     by hkr HFr KR5
                 | st_ok _ _ _ (restrict _ ?msn) =>
                   assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                     by hkr HFr KR5 end.
                 lazymatch type of HS with
                 | st_ok_pi _ _ ?Ex _ _ =>
                   assert (X32 : ew Ex 32 = Z_to_bv 64 (p_d cx))
                     by (rewrite !ew_ewset_other by lia; exact (EX 0%nat ltac:(lia)));
                   rewrite branch_ne_U, (U_atom Ex 32 (p_d cx) X32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc
                 | st_ok _ ?Ex _ _ =>
                   assert (X32 : ew Ex 32 = Z_to_bv 64 (p_d cx))
                     by (rewrite !ew_ewset_other by lia; exact (EX 0%nat ltac:(lia)));
                   rewrite branch_ne_U, (U_atom Ex 32 (p_d cx) X32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc end.
                 apply negb_false_iff, Z.eqb_eq in Hc.
                 clear HF HFr HG0 KR5.
                 prreg HS (1%bv : bv 5) Z1; prreg HS (2%bv : bv 5) Z2; prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4;
                 prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9; prreg HS (10%bv : bv 5) Z10; prreg HS (19%bv : bv 5) Z19;
                 prreg HS (20%bv : bv 5) Z20; prreg HS (21%bv : bv 5) Z21; prreg HS (23%bv : bv 5) Z23;
                 prreg HS (25%bv : bv 5) Z25; prreg HS (27%bv : bv 5) Z27;
                 try rewrite !ew_ewset_other in Z2, Z3, Z4, Z8, Z9, Z19, Z20, Z23, Z25, Z27 by lia;
                 rewrite (EE 2%nat 2%bv eq_refl), G2 in Z2; rewrite (EE 3%nat 3%bv eq_refl), G3 in Z3;
                 rewrite (EE 4%nat 4%bv eq_refl), G4 in Z4; rewrite (EE 8%nat 8%bv eq_refl), G8 in Z8;
                 rewrite (EE 9%nat 9%bv eq_refl), G9 in Z9; rewrite (EE 19%nat 19%bv eq_refl), R19 in Z19;
                 rewrite (EE 20%nat 20%bv eq_refl), R20 in Z20; rewrite (EE 23%nat 23%bv eq_refl), R23 in Z23;
                 rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25; rewrite (EE 27%nat 27%bv eq_refl), G27 in Z27.
                 assert (X32' : ew E 32 = Z_to_bv 64 (p_d cx)) by exact (EX 0%nat ltac:(lia)).
                 rewrite X32', (h_sll3 (p_d cx) ltac:(lia)) in Z21.
                 assert (Z10' : getr (ms_regs _) 10 = w64 (p_bn cx))
                   by (rewrite Z10; unfold p_bn, p_cap; rewrite Hc; reflexivity).
                 assert (Z21' : getr (ms_regs _) 21 = w64 (p_cap cx)) by (rewrite Z21; unfold p_cap; reflexivity).
                 pmkst HS. rewrite (pal_malloc B TL).
                 refine (h_B_malloc POST HK3 cx fp k acc ly3 S3 W3 ms3 md3 b h _ _ _ HB HJ3 HFR HMO HBODY Hn26 Hfds Hfs
                   SD SGLEN SPSP (conj HGL2 HGL4) Hgood Hk2 Hacc2 HPERM (conj HPSO1 HPSO2) HPSF HSRC HJ
                   (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))
                   Z1 Z2 Z3 Z4 Z8 Z9 Z10' Z19 Z20 Z21' Z23 Z25 Z27 KR6).
        -- (* not taken: a0 = 0 *)
           exfalso.
           lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
             assert (X10 : ew Ex 10 = Z_to_bv 64 0)
               by (rewrite !ew_ewset_other by lia; rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity);
             rewrite branch_eq_U, (U_atom Ex 10 0 X10 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc end.
           cbn in Hc. discriminate Hc.
    + (* 0x80a3c not taken: the magic is A1B2C3D4 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
        assert (EMa : U Ex h_magic_sv = PST.pcap_magic (p_F cx) + h_magic_X cx)
          by (apply EB; intros n Hn; rewrite !ew_ewset_other by lia; reflexivity);
        unfold h_magic_sv in EMa;
        rewrite branch_ne_U, EMa, (U_lit Ex 18446744072127431636 ltac:(lia)) in Hc end.
      apply negb_false_iff, Z.eqb_eq in Hc.
      assert (HMg : PST.pcap_magic (p_F cx) = 2712847316) by (exact (proj1 (proj1 (h_U_K cx)) Hc)).
      assert (HSw : p_swz cx = 0) by (unfold p_swz, PST.pcap_sw; rewrite HMg; reflexivity).
      clear Hc.
      paj_run_tok RUNX HS HJ SHOK hBspan.
      { hawr0. }
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
        assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
          by hkr HFr KR1 end.
      clear HF HFr HG0 KR1.
      psrr_branch_tok RUNX BRX HS SHOK hBspan.
      * (* 0x80a40 beqz a0: taken, the open accepted *)
        paj_run_tok RUNX HS HJ SHOK hBspan.
        { hawr0. }
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
          assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
            by hkr HFr KR2 end.
        clear HF HFr HG0 KR2 Hc.
        psrr_branch_tok RUNX BRX HS SHOK hBspan.
        -- (* 0x80aa0 bne ps.swapped, seqz to PP_abort (0x80a74 decided by 0x80a40's condition): both are 0 here *)
           exfalso.
           lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
             assert (X38 : ew Ex 38 = Z_to_bv 64 (p_swz cx))
               by (rewrite !ew_ewset_other by lia; exact (EX 6%nat ltac:(lia)));
             rewrite branch_ne_U, (U_atom Ex 38 (p_swz cx) X38 ltac:(rewrite HSw; lia)) in Hc end.
           rewrite HSw in Hc. rewrite ?U_SAlu, ?U_SLit in Hc. vm_compute in Hc. discriminate Hc.
        -- (* 0x80aa0 not taken: on to the record buffer's malloc *)
           paj_run_tok RUNX HS HJ SHOK hBspan.
           { hawr0. }
           lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
             assert (KR5 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
               by hkr HFr KR3 end.
           clear HF HFr HG0 KR3 Hc.
           psrr_branch_tok RUNX BRX HS SHOK hBspan.
           ** (* 0x80ab0 bnez d: the capacity is 8 d *)
              paj_run_tok RUNX HS HJ SHOK hBspan.
              { hawr0. }
              lazymatch type of HS with
              | st_ok_pi _ _ _ _ (restrict _ ?msn) =>
                assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                  by hkr HFr KR5
              | st_ok _ _ _ (restrict _ ?msn) =>
                assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                  by hkr HFr KR5 end.
              lazymatch type of HS with
              | st_ok_pi _ _ ?Ex _ _ =>
                assert (X32 : ew Ex 32 = Z_to_bv 64 (p_d cx))
                  by (rewrite !ew_ewset_other by lia; exact (EX 0%nat ltac:(lia)));
                rewrite branch_ne_U, (U_atom Ex 32 (p_d cx) X32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc
              | st_ok _ ?Ex _ _ =>
                assert (X32 : ew Ex 32 = Z_to_bv 64 (p_d cx))
                  by (rewrite !ew_ewset_other by lia; exact (EX 0%nat ltac:(lia)));
                rewrite branch_ne_U, (U_atom Ex 32 (p_d cx) X32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc end.
              apply negb_true_iff, Z.eqb_neq in Hc.
              clear HF HFr HG0 KR5.
              prreg HS (1%bv : bv 5) Z1; prreg HS (2%bv : bv 5) Z2; prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4;
              prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9; prreg HS (10%bv : bv 5) Z10; prreg HS (19%bv : bv 5) Z19;
              prreg HS (20%bv : bv 5) Z20; prreg HS (21%bv : bv 5) Z21; prreg HS (23%bv : bv 5) Z23;
              prreg HS (25%bv : bv 5) Z25; prreg HS (27%bv : bv 5) Z27;
              try rewrite !ew_ewset_other in Z2, Z3, Z4, Z8, Z9, Z19, Z20, Z23, Z25, Z27 by lia;
              rewrite (EE 2%nat 2%bv eq_refl), G2 in Z2; rewrite (EE 3%nat 3%bv eq_refl), G3 in Z3;
              rewrite (EE 4%nat 4%bv eq_refl), G4 in Z4; rewrite (EE 8%nat 8%bv eq_refl), G8 in Z8;
              rewrite (EE 9%nat 9%bv eq_refl), G9 in Z9; rewrite (EE 19%nat 19%bv eq_refl), R19 in Z19;
              rewrite (EE 20%nat 20%bv eq_refl), R20 in Z20; rewrite (EE 23%nat 23%bv eq_refl), R23 in Z23;
              rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25; rewrite (EE 27%nat 27%bv eq_refl), G27 in Z27.
              assert (X32' : ew E 32 = Z_to_bv 64 (p_d cx)) by exact (EX 0%nat ltac:(lia)).
              rewrite X32', (h_sll3 (p_d cx) ltac:(lia)) in Z10, Z21.
              assert (Z10' : getr (ms_regs _) 10 = w64 (p_bn cx))
                by (rewrite Z10; unfold p_bn, p_cap; rewrite Z.max_l by lia; reflexivity).
              assert (Z21' : getr (ms_regs _) 21 = w64 (p_cap cx)) by (rewrite Z21; unfold p_cap; reflexivity).
              pmkst HS. rewrite (pal_malloc B TL).
              refine (h_B_malloc POST HK3 cx fp k acc ly3 S3 W3 ms3 md3 b h _ _ _ HB HJ3 HFR HMO HBODY Hn26 Hfds Hfs
                SD SGLEN SPSP (conj HGL2 HGL4) Hgood Hk2 Hacc2 HPERM (conj HPSO1 HPSO2) HPSF HSRC HJ
                (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))
                Z1 Z2 Z3 Z4 Z8 Z9 Z10' Z19 Z20 Z21' Z23 Z25 Z27 KR6).
           ** (* d = 0: the harness asks for one byte *)
              paj_run_tok RUNX HS HJ SHOK hBspan.
              { hawr0. }
              lazymatch type of HS with
              | st_ok_pi _ _ _ _ (restrict _ ?msn) =>
                assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                  by hkr HFr KR5
              | st_ok _ _ _ (restrict _ ?msn) =>
                assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                  by hkr HFr KR5 end.
              lazymatch type of HS with
              | st_ok_pi _ _ ?Ex _ _ =>
                assert (X32 : ew Ex 32 = Z_to_bv 64 (p_d cx))
                  by (rewrite !ew_ewset_other by lia; exact (EX 0%nat ltac:(lia)));
                rewrite branch_ne_U, (U_atom Ex 32 (p_d cx) X32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc
              | st_ok _ ?Ex _ _ =>
                assert (X32 : ew Ex 32 = Z_to_bv 64 (p_d cx))
                  by (rewrite !ew_ewset_other by lia; exact (EX 0%nat ltac:(lia)));
                rewrite branch_ne_U, (U_atom Ex 32 (p_d cx) X32 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc end.
              apply negb_false_iff, Z.eqb_eq in Hc.
              clear HF HFr HG0 KR5.
              prreg HS (1%bv : bv 5) Z1; prreg HS (2%bv : bv 5) Z2; prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4;
              prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9; prreg HS (10%bv : bv 5) Z10; prreg HS (19%bv : bv 5) Z19;
              prreg HS (20%bv : bv 5) Z20; prreg HS (21%bv : bv 5) Z21; prreg HS (23%bv : bv 5) Z23;
              prreg HS (25%bv : bv 5) Z25; prreg HS (27%bv : bv 5) Z27;
              try rewrite !ew_ewset_other in Z2, Z3, Z4, Z8, Z9, Z19, Z20, Z23, Z25, Z27 by lia;
              rewrite (EE 2%nat 2%bv eq_refl), G2 in Z2; rewrite (EE 3%nat 3%bv eq_refl), G3 in Z3;
              rewrite (EE 4%nat 4%bv eq_refl), G4 in Z4; rewrite (EE 8%nat 8%bv eq_refl), G8 in Z8;
              rewrite (EE 9%nat 9%bv eq_refl), G9 in Z9; rewrite (EE 19%nat 19%bv eq_refl), R19 in Z19;
              rewrite (EE 20%nat 20%bv eq_refl), R20 in Z20; rewrite (EE 23%nat 23%bv eq_refl), R23 in Z23;
              rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25; rewrite (EE 27%nat 27%bv eq_refl), G27 in Z27.
              assert (X32' : ew E 32 = Z_to_bv 64 (p_d cx)) by exact (EX 0%nat ltac:(lia)).
              rewrite X32', (h_sll3 (p_d cx) ltac:(lia)) in Z21.
              assert (Z10' : getr (ms_regs _) 10 = w64 (p_bn cx))
                by (rewrite Z10; unfold p_bn, p_cap; rewrite Hc; reflexivity).
              assert (Z21' : getr (ms_regs _) 21 = w64 (p_cap cx)) by (rewrite Z21; unfold p_cap; reflexivity).
              pmkst HS. rewrite (pal_malloc B TL).
              refine (h_B_malloc POST HK3 cx fp k acc ly3 S3 W3 ms3 md3 b h _ _ _ HB HJ3 HFR HMO HBODY Hn26 Hfds Hfs
                SD SGLEN SPSP (conj HGL2 HGL4) Hgood Hk2 Hacc2 HPERM (conj HPSO1 HPSO2) HPSF HSRC HJ
                (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))
                Z1 Z2 Z3 Z4 Z8 Z9 Z10' Z19 Z20 Z21' Z23 Z25 Z27 KR6).
      * exfalso.
        lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
          assert (X10 : ew Ex 10 = Z_to_bv 64 0)
            by (rewrite !ew_ewset_other by lia; rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity);
          rewrite branch_eq_U, (U_atom Ex 10 0 X10 ltac:(lia)), (U_lit Ex 0 ltac:(lia)) in Hc end.
        cbn in Hc. discriminate Hc.
  - (* refused: a0 = -1, ps.f = 0, no FILE *)
    unfold pval, pPS, PO_PS in HPSN.
    destruct (Z_lt_le_dec (p_nF cx) 4) as [Hsmall | Hbig].
    + destruct (HSgen false false ltac:(intros e; discriminate e)
        ltac:(intros _; split; [exact R10 | split; [exact HPSN | split; [intros e; discriminate e | intros _; exact Hsmall]]])
        ltac:(intros e; discriminate e)) as [HS SHOK].
      paj_run_tok RUNX HS HJ SHOK hBspan.
      { hawr0. }
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
        assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
          by (let aa := fresh "a" in let Haa := fresh "Ha" in intros aa Haa;
              exact (h_kept_nowin _ _ _ _ _ HFr ltac:(clear; vm_compute; repeat constructor) aa Haa)) end.
      clear HF HFr HG0.
      psrr_branch_tok RUNX BRX HS SHOK hBspan.
      * (* 0x80a50 beq a0, a2 taken: a0 = -1 = a2 *)
        paj_run_tok RUNX HS HJ SHOK hBspan.
        { hawr0. }
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
          assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
            by hkr HFr KR1
        | st_ok _ _ _ (restrict _ ?msn) =>
          assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
            by hkr HFr KR1 end.
        clear HF HFr HG0 KR1 Hc.
        rename KR2 into KRF.
        prreg HS (1%bv : bv 5) Z1; prreg HS (2%bv : bv 5) Z2; prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4;
        prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9; prreg HS (10%bv : bv 5) Z10; prreg HS (20%bv : bv 5) Z20;
        prreg HS (23%bv : bv 5) Z23; prreg HS (25%bv : bv 5) Z25; prreg HS (27%bv : bv 5) Z27;
        try rewrite !ew_ewset_other in Z2, Z3, Z4, Z8, Z9, Z10, Z20, Z23, Z25, Z27 by lia;
        rewrite (EE 2%nat 2%bv eq_refl), G2 in Z2; rewrite (EE 3%nat 3%bv eq_refl), G3 in Z3;
        rewrite (EE 4%nat 4%bv eq_refl), G4 in Z4; rewrite (EE 8%nat 8%bv eq_refl), G8 in Z8;
        rewrite (EE 9%nat 9%bv eq_refl), G9 in Z9; rewrite (EE 19%nat 19%bv eq_refl), R19 in Z10;
        rewrite (EE 20%nat 20%bv eq_refl), R20 in Z20; rewrite (EE 23%nat 23%bv eq_refl), R23 in Z23;
        rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25; rewrite (EE 27%nat 27%bv eq_refl), G27 in Z27.
        pmkst HS. rewrite (pal_free B TL).
        exact (h_B_free POST HK12r cx fp k acc ly3 S3 W3 ms3 md3 b _ _ _ HB HJ3 HFR HMO HBODY Hn26 Hfds Hfs Hk2 Hacc2
          HPERM HSN HJ (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))
          Z1 Z2 Z3 Z4 Z8 Z9 Z10 Z20 Z23 Z25 Z27 KRF).
      * (* not taken: a0 = -1 = a2, impossible *)
        exfalso.
        lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
          hx10 Ex R10 EE X10;
          rewrite branch_eq_U, (U_atom Ex 10 _ X10 ltac:(lia)), (U_lit Ex 18446744073709551615 ltac:(lia)) in Hc end.
        rewrite Z.eqb_refl in Hc. discriminate Hc.
    + destruct (HSgen true false ltac:(intros e; discriminate e)
        ltac:(intros _; split; [exact R10 | split; [exact HPSN | split; [intros _; exact Hbig | intros e; discriminate e]]])
        ltac:(intros e; discriminate e)) as [HS SHOK].
      paj_run_tok RUNX HS HJ SHOK hBspan.
      { hawr0. }
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
        assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
          by (let aa := fresh "a" in let Haa := fresh "Ha" in intros aa Haa;
              exact (h_kept_nowin _ _ _ _ _ HFr ltac:(clear; vm_compute; repeat constructor) aa Haa)) end.
      clear HF HFr HG0.
      psrr_branch_tok RUNX BRX HS SHOK hBspan.
      * (* 0x80a30 bltu len, 24 taken *)
        paj_run_tok RUNX HS HJ SHOK hBspan.
        { hawr0. }
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
          assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
            by hkr HFr KR1 end.
        clear HF HFr HG0 KR1 Hc.
        psrr_branch_tok RUNX BRX HS SHOK hBspan.
        -- (* 0x80a70 bne a0, a2 to PP_abort: a0 = -1 = a2, impossible *)
           exfalso.
           lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
             hx10 Ex R10 EE X10;
             rewrite branch_ne_U, (U_atom Ex 10 _ X10 ltac:(lia)), (U_lit Ex 18446744073709551615 ltac:(lia)) in Hc end.
           rewrite Z.eqb_refl in Hc. discriminate Hc.
        -- paj_run_tok RUNX HS HJ SHOK hBspan.
           { hawr0. }
           lazymatch type of HS with
           | st_ok_pi _ _ _ _ (restrict _ ?msn) =>
             assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
               by hkr HFr KR2
           | st_ok _ _ _ (restrict _ ?msn) =>
             assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
               by hkr HFr KR2 end.
           clear HF HFr HG0 KR2 Hc.
           rename KR3 into KRF.
           prreg HS (1%bv : bv 5) Z1; prreg HS (2%bv : bv 5) Z2; prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4;
           prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9; prreg HS (10%bv : bv 5) Z10; prreg HS (20%bv : bv 5) Z20;
           prreg HS (23%bv : bv 5) Z23; prreg HS (25%bv : bv 5) Z25; prreg HS (27%bv : bv 5) Z27;
           try rewrite !ew_ewset_other in Z2, Z3, Z4, Z8, Z9, Z10, Z20, Z23, Z25, Z27 by lia;
           rewrite (EE 2%nat 2%bv eq_refl), G2 in Z2; rewrite (EE 3%nat 3%bv eq_refl), G3 in Z3;
           rewrite (EE 4%nat 4%bv eq_refl), G4 in Z4; rewrite (EE 8%nat 8%bv eq_refl), G8 in Z8;
           rewrite (EE 9%nat 9%bv eq_refl), G9 in Z9; rewrite (EE 19%nat 19%bv eq_refl), R19 in Z10;
           rewrite (EE 20%nat 20%bv eq_refl), R20 in Z20; rewrite (EE 23%nat 23%bv eq_refl), R23 in Z23;
           rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25; rewrite (EE 27%nat 27%bv eq_refl), G27 in Z27.
           pmkst HS. rewrite (pal_free B TL).
           exact (h_B_free POST HK12r cx fp k acc ly3 S3 W3 ms3 md3 b _ _ _ HB HJ3 HFR HMO HBODY Hn26 Hfds Hfs Hk2 Hacc2
             HPERM HSN HJ (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))
             Z1 Z2 Z3 Z4 Z8 Z9 Z10 Z20 Z23 Z25 Z27 KRF).
      * (* not taken: len >= 24 *)
        lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
          assert (X33 : ew Ex 33 = Z_to_bv 64 (p_nF cx))
            by (rewrite ?ew_ewset_other by lia; exact (EX 1%nat ltac:(lia)));
          rewrite branch_ltu_U, (U_atom Ex 33 _ X33 ltac:(lia)), (U_lit Ex 24 ltac:(lia)) in Hc end.
        apply Z.ltb_ge in Hc. rename Hc into H24.
        destruct (h_bad_magic cx Hgood H24) as [HnK1 HnK2].
        paj_run_tok RUNX HS HJ SHOK hBspan.
        { hawr0. }
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
          assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
            by hkr HFr KR1 end.
        clear HF HFr HG0 KR1.
        psrr_branch_tok RUNX BRX HS SHOK hBspan.
        -- (* 0x80a3c bne magic, A1B2C3D4 taken *)
           clear Hc.
           paj_run_tok RUNX HS HJ SHOK hBspan.
           { hawr0. }
           lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
             assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
               by hkr HFr KR2 end.
           clear HF HFr HG0 KR2.
           psrr_branch_tok RUNX BRX HS SHOK hBspan.
           ++ (* 0x80a70 bne a0, a2: a2 = seqz (magic xor D4C3B2A1) - 1 = -1 = a0, impossible *)
              exfalso.
              lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
                assert (EMb : U Ex h_magic_sv = PST.pcap_magic (p_F cx) + h_magic_X cx)
                  by (apply EB; intros n Hn; rewrite !ew_ewset_other by lia; reflexivity);
                hx10 Ex R10 EE X10;
                pose proof (h_a2_U Ex _ EMb) as HA2; unfold h_seqz_sv, h_magic_sv, h_K2 in HA2;
                rewrite branch_ne_U, (U_atom Ex 10 _ X10 ltac:(lia)), HA2 in Hc end.
              destruct (Z.eqb_spec (PST.pcap_magic (p_F cx) + h_magic_X cx) h_K2) as [EK | NK].
              ** exfalso. exact (HnK2 (proj1 (proj2 (h_U_K cx)) EK)).
              ** unfold h_K2 in NK. apply Z.eqb_neq in NK. rewrite NK in Hc. rewrite Z.eqb_refl in Hc. discriminate Hc.
           ++ paj_run_tok RUNX HS HJ SHOK hBspan.
              { hawr0. }
              lazymatch type of HS with
              | st_ok_pi _ _ _ _ (restrict _ ?msn) =>
                assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                  by hkr HFr KR3
              | st_ok _ _ _ (restrict _ ?msn) =>
                assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
                  by hkr HFr KR3 end.
              clear HF HFr HG0 KR3 Hc.
              rename KR4 into KRF.
              prreg HS (1%bv : bv 5) Z1; prreg HS (2%bv : bv 5) Z2; prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4;
              prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9; prreg HS (10%bv : bv 5) Z10; prreg HS (20%bv : bv 5) Z20;
              prreg HS (23%bv : bv 5) Z23; prreg HS (25%bv : bv 5) Z25; prreg HS (27%bv : bv 5) Z27;
              try rewrite !ew_ewset_other in Z2, Z3, Z4, Z8, Z9, Z10, Z20, Z23, Z25, Z27 by lia;
              rewrite (EE 2%nat 2%bv eq_refl), G2 in Z2; rewrite (EE 3%nat 3%bv eq_refl), G3 in Z3;
              rewrite (EE 4%nat 4%bv eq_refl), G4 in Z4; rewrite (EE 8%nat 8%bv eq_refl), G8 in Z8;
              rewrite (EE 9%nat 9%bv eq_refl), G9 in Z9; rewrite (EE 19%nat 19%bv eq_refl), R19 in Z10;
              rewrite (EE 20%nat 20%bv eq_refl), R20 in Z20; rewrite (EE 23%nat 23%bv eq_refl), R23 in Z23;
              rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25; rewrite (EE 27%nat 27%bv eq_refl), G27 in Z27.
              pmkst HS. rewrite (pal_free B TL).
              exact (h_B_free POST HK12r cx fp k acc ly3 S3 W3 ms3 md3 b _ _ _ HB HJ3 HFR HMO HBODY Hn26 Hfds Hfs Hk2 Hacc2
                HPERM HSN HJ (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))
                Z1 Z2 Z3 Z4 Z8 Z9 Z10 Z20 Z23 Z25 Z27 KRF).
        -- (* not taken: the magic is A1B2C3D4, so the file is good: impossible *)
           exfalso.
           lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
             assert (EMa : U Ex h_magic_sv = PST.pcap_magic (p_F cx) + h_magic_X cx)
               by (apply EB; intros n Hn; rewrite !ew_ewset_other by lia; reflexivity);
             unfold h_magic_sv in EMa;
             rewrite branch_ne_U, EMa, (U_lit Ex 18446744072127431636 ltac:(lia)) in Hc end.
           apply negb_false_iff, Z.eqb_eq in Hc.
           exact (HnK1 (proj1 (proj1 (h_U_K cx)) Hc)).
Qed.

End c.
End b.
End a.

