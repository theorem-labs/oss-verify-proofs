(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 574 of its 653 lines of code are new or changed and 1472 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeHead.v, with its module names changed; 1183 of its 1234 lines of code are new or changed and 602 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's phase +0x194 -> +0x3b4 (a segment of kernel's walk, link-a/plan/kernel-plan.md
   (internal record, sha256 440bf3b40ab7) section 4), part 1: the symbolic state at the phase start (kin_poison), the facts every part
   of the phase reads off the cut, and the end of the phase (kin_err) from the facts a run gives. The run itself is kernel_flags.v.

   WHAT THE CODE DOES (listing (internal path) (internal record, sha256 7bc02d6772b3), offsets
   from kernel's entry 0x83d30):
   - +0x194 .. +0x218: a1 := 0xf3, a0 := s2 + 8, 32 stores of 0xf3 at s6 + 0x428 .. s6 + 0x447 (F's right
     redzone, s6 = shadow(F));
   - +0x21c .. +0x230: s8 := shadow(a0 + 8), the instrumented check of the cursor's n (no slow path), slot 0xb0 :=
     a0 + 8; +0x234 a6 := n; a2 := nl_errno.e (0x21080, A_OBJ 15), a1 := a0 >> 3;
   - three times fuzz_u8 (flags, the e index byte, the end index byte): n = 0 ends it (+0x2fc: flags 0, e 105
     folded, end 0; +0x30c: e[0]; +0x3b0: end 0); else the two cursor checks, [a0 + 8] := n - 1, [a0] := p + 1,
     the one-byte check of the input byte at p (its slow path +0x21c8 / +0x21fc / +0x220c: (p & 7) < s), `lbu`;
     the e byte b -> b % 6 (mul by 0xab, >> 10) -> `lw a5` at nl_errno.e + 4 (b % 6) (+0x340, its 4-byte check
     +0x334 with the slow path +0x21d8); the end byte b -> a0 := b % 6.
   At +0x3b4 (kin_err): a3 = flags, a5 = e, a0 = end index, a2 = nl_errno.e, a1 = a0 >> 3, s8 = shadow(a0 + 8),
   slot 0xb0 = a0 + 8, F's shadow kfsh f8 f8 f3, the cursor advanced by 0..3.

   THE SYMBOLIC STATE (probed: the engine runs as described above). Atoms 0..31 = the registers at the cut, 32 = p,
   33 = n (the cursor's words), 34..36 = shadow(p + i), 37..39 = the shadow bytes there, 40..42 = the input bytes
   d[i] (i = 0, 1, 2), 256 = A_OBJ 15 (nl_errno.e). Bx = SOff 20 0 (s4). The cursor's checks pass by the shadow
   entry [a0, a0 + 16) (range_addressable of the cursor), nl_errno.e's by the entry [0x21080, 0x21098) (its atom
   8-aligned, so the token of e[5] at +0x334 granulates into the entry). The input byte's check has a slow path the
   engine's token cannot take, so each input check is run on a region holding the shadow byte (atom 37 + i, its
   value 0 or > p & 7 by range_addressable) and both arms are walked.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK1d YG0q YF0v PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkZsh LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI01 YK00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* every lemma of the phase takes all the Section hypotheses (SK B LAWS LV TB TL), so its files call it uniformly *)
Set Default Proof Using "All".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at +0x194 ---- *)
Definition kfl_Bx : sv := SOff 20 0.
(* the F-shadow stores (+0x19c .. +0x218) run with no instrumented check and a span no window meets *)
Definition kfl_span1 : Z * Z := (2 ^ 64 - 2, 2 ^ 64 - 2).
Definition kfl_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition kfl_SH : list shent := [mkSHE 18 0 16; mkSHE (A_OBJ 15) 0 24].

Definition kfl_rF : YP09.region := YP09.mkRegion (Some 22%nat) 0x428 0x448 0x428 0x448 [].
Definition kfl_rS : YP09.region := YP09.mkRegion (Some 9%nat) 0xb0 0xb8 0xb0 0xb8 [].
Definition kfl_rC : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 0 16
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition kfl_rE : YP09.region := YP09.mkRegion (Some (A_OBJ 15)) 0 24 0 0
  [YP09.mkChunk 0 (CVal 4 (SLit 105)); YP09.mkChunk 4 (CVal 4 (SLit 4)); YP09.mkChunk 8 (CVal 4 (SLit 11));
   YP09.mkChunk 12 (CVal 4 (SLit 1)); YP09.mkChunk 16 (CVal 4 (SLit 24)); YP09.mkChunk 20 (CVal 4 (SLit 111))].
(* the shadow byte of p + i (atom 34 + i, its value atom 37 + i) and the input byte d[i] (atom 40 + i) *)
Definition kfl_rQ (i : nat) : YP09.region :=
  YP09.mkRegion (Some (34 + i)%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (37 + i) 0))].
Definition kfl_rD (i : nat) : YP09.region :=
  YP09.mkRegion (Some 32%nat) (Z.of_nat i) (Z.of_nat i + 1) 0 0 [YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (40 + i) 0))].

Definition kfl_facts0 : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (18%nat, mkAF 0 (2 ^ 47 - 16) 0); (22%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
           (32%nat, mkAF 0 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0);
           (A_OBJ 15, mkAF 0x21080 0x21080 3)] [] [].
Definition kfl_ss0 : sstate := mkSS (kpc KP_POISON) sr_atoms [kfl_rF; kfl_rS; kfl_rC] None kfl_facts0.

Lemma kfl_forall3 : forall {A} (P : A -> Prop) a b c, Forall P [a; b; c] -> P a /\ P b /\ P c.
Proof.
  intros A P a b c H. inversion H as [|? ? Ha H1]; subst. inversion H1 as [|? ? Hb H2]; subst.
  inversion H2 as [|? ? Hc _]; subst. auto.
Qed.

(* x is outside the frame [F, F + 8 k) (F 8-aligned): its shadow byte is outside the frame's shadow *)
Lemma kfl_shadow_out : forall F x k, F mod 8 = 0 -> 0 <= F -> 0 <= x -> ~ (F <= x < F + 8 * k) ->
  ~ (SHADOW_OFF + F / 8 <= SHADOW_OFF + x / 8 < SHADOW_OFF + F / 8 + k).
Proof.
  intros F x k HF HF0 Hx0 Hn Hs. apply Hn.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. lia.
Qed.

(* a word read through the reader is the word at the same place of a reader that agrees on its 8 bytes *)
Lemma kfl_rdword_eq : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  rewrite <- (Z.add_0_r a) at 1 2. rewrite !H by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(* ---- the values of the engine's expressions ---- *)
Ltac kfl_ew := cbn [ew ewset Nat.eqb].

(* the shadow cell of an atom plus c: ((x + c) >> 3) + s4 *)
Definition kfl_e_sh (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 20 0).
Definition kfl_e_a1 : sv := SAlu ALU_SRL (SOff 18 0) (SLit 3).
(* b % 6 for a byte b (+0x2d8 .. +0x2f4 and +0x38c .. +0x3a8: mul by 0xab, >> 10, b - 6 q, & 0xff) *)
Definition kfl_m6 (n : nat) : sv :=
  SAlu ALU_AND
    (SAlu ALU_ADD (SOff n 0)
       (SAlu ALU_SUB
          (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff n 0) (SLit 171)) (SLit 10)) (SLit 1))
          (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff n 0) (SLit 171)) (SLit 10)) (SLit 3))))
    (SLit 255).
Definition kfl_m6f (w : word) : word := sv_denot (mkEnv (fun _ => w) (fun _ => [])) (kfl_m6 0).

Lemma kfl_den_off : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c Hn Hv. cbn [sv_denot]. rewrite Hn. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma kfl_den_srl3 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = Z_to_bv 64 (v / 8).
Proof.
  intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3.
  rewrite (U_atom_off E n v 0 Hn Hv ltac:(lia)). rewrite Z.add_0_r, Z.shiftr_div_pow2 by lia.
  change (2 ^ 3) with 8. apply zcanon_id. unfold M64. lia.
Qed.

Lemma kfl_den_sh : forall E n c v base,
  ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> ew E 20 = w64 base -> 0 <= base ->
  base + (v + c) / 8 < 2 ^ 64 ->
  sv_denot E (kfl_e_sh n c) = Z_to_bv 64 (base + (v + c) / 8).
Proof.
  intros E n c v base Hn Hv Hvc Hm Hb Hs. unfold kfl_e_sh. rewrite denot_lit_U. f_equal.
  assert (Hd : 0 <= (v + c) / 8 <= v + c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3.
  rewrite (U_atom_off E n v c Hn Hv Hvc), (U_atom_off E 20 base 0 Hm ltac:(lia) ltac:(lia)).
  rewrite Z.add_0_r, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma kfl_den_and7 : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit 7)) = Z_to_bv 64 ((v + c) mod 8).
Proof.
  intros E n v c Hn Hv Hvc. rewrite denot_lit_U. f_equal.
  rewrite U_and_lit by lia. rewrite (U_atom_off E n v c Hn Hv Hvc).
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma kfl_m6_env : forall E n, sv_denot E (kfl_m6 n) = kfl_m6f (ew E n).
Proof. intros E n. reflexivity. Qed.

Lemma kfl_m6_tab : forallb (fun x => Z.eqb (bv_unsigned (kfl_m6f (Z_to_bv 64 x))) (x mod 6))
  (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma kfl_den_m6 : forall E n x, ew E n = w64 x -> 0 <= x < 256 -> sv_denot E (kfl_m6 n) = Z_to_bv 64 (x mod 6).
Proof.
  intros E n x Hn Hx. rewrite kfl_m6_env, Hn. unfold w64.
  assert (Hin : In x (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia]. }
  pose proof (proj1 (forallb_forall _ _) kfl_m6_tab x Hin) as H. cbv beta in H. apply Z.eqb_eq in H.
  rewrite <- (Z_to_bv_bv_unsigned _ (kfl_m6f (Z_to_bv 64 x))), H. reflexivity.
Qed.

Lemma kfl_beq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold branch_taken, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma kfl_bge : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof.
  intros x y Hx Hy. cbn [branch_taken]. try unfold c_lts. unfold bv_lts.
  rewrite !bv_signed_small by lia. reflexivity.
Qed.

Lemma kfl_getr : forall (rg : bvmap 5 word) (r : nat) (b : bv 5) v,
  Z_to_bv 5 (Z.of_nat r) = b -> getr rg (Z_to_bv 5 (Z.of_nat r)) = v -> getr rg b = v.
Proof. intros rg r b v <- H. exact H. Qed.

Lemma kfl_kfsh_lo : forall i a b r r', (i < 0x428)%nat -> nth i (kfsh a b r) 0 = nth i (kfsh a b r') 0.
Proof.
  intros i a b r r' Hi. unfold kfsh. rewrite !app_assoc.
  rewrite (app_nth1 _ (repeat r 32)), (app_nth1 _ (repeat r' 32)); [reflexivity | |];
    rewrite !length_app, !repeat_length; lia.
Qed.

Lemma kfl_kfsh_hi : forall i a b r, (0x428 <= i < 0x448)%nat -> nth i (kfsh a b r) 0 = r.
Proof.
  intros i a b r Hi. unfold kfsh. rewrite !app_assoc.
  rewrite app_nth2 by (rewrite !length_app, !repeat_length; lia).
  apply (repeat_spec 32 r). apply nth_In. rewrite !length_app, !repeat_length. lia.
Qed.

(* the regions of a cut of the phase: the slot 0xb0 holding a0 + 8, the cursor advanced by adv *)
Definition kfl_rS1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xb0 0xb8 0xb0 0xb8 [YP09.mkChunk 0xb0 (CVal 8 (SOff 18 8))].
Definition kfl_rCa (adv : Z) : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 0 16
  [YP09.mkChunk 0 (CVal 8 (SOff 32 adv)); YP09.mkChunk 8 (CVal 8 (SOff 33 (- adv)))].
Definition kfl_factsM : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (18%nat, mkAF 0 (2 ^ 47 - 16) 0); (32%nat, mkAF 0 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0);
           (A_OBJ 15, mkAF 0x21080 0x21080 3)] [] [].
Definition kfl_ssM (pc adv : Z) (rs : list YP09.region) : sstate :=
  mkSS (kpc pc) sr_atoms ([kfl_rS1; kfl_rCa adv] ++ rs) None kfl_factsM.

Definition kfl_regsP (E : env) (ss : sstate) (rl : list (nat * Z)) : Prop :=
  Forall (fun rv => sv_denot E (sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat (fst rv)))) = w64 (snd rv)) rl.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.   (* the lib/A frame *)
Hypothesis LV : LinkVals.               (* by computation at the certified instance *)
Hypothesis TL : PALib B.                (* lib/A/Prog/LinkPaLib.v, of the lib/A frame *)
Hypothesis TB : PcapSyms B.             (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)

(* ---- the atoms 32.. of the start environment ---- *)
Definition kfl_q (cx : kcx) (i : Z) : Z := SHADOW_OFF + (k_wp cx + i) / 8.
Definition kfl_s (cx : kcx) (W3 : world SEGS) (ms : machine_state) (i : Z) : Z :=
  match aview SEGS (w_H W3) (ms_mem ms) (kfl_q cx i) with Some v => v | None => 0 end.
Definition kfl_d (cx : kcx) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) (k_d cx) (Z_to_bv 8 0)).
Definition kfl_ext (cx : kcx) (W3 : world SEGS) (ms : machine_state) : list word :=
  [w64 (k_wp cx); w64 (k_wn cx); w64 (kfl_q cx 0); w64 (kfl_q cx 1); w64 (kfl_q cx 2);
   w64 (kfl_s cx W3 ms 0); w64 (kfl_s cx W3 ms 1); w64 (kfl_s cx W3 ms 2);
   w64 (kfl_d cx 0); w64 (kfl_d cx 1); w64 (kfl_d cx 2)].
Definition kfl_E0 (cx : kcx) (W3 : world SEGS) (ms : machine_state) : env :=
  Eimg (Ereg (ms_regs ms) (kfl_ext cx W3 ms)).

(* ---- the phase's context: the cut kin_poison at ms0, and the next phase ---- *)
Definition kfl_C (POST : kcx -> world SEGS -> config -> Prop) (cx : kcx) (fpos k2 : Z) (ly3 : alayout)
  (S3 : astate) (W3 : world SEGS) (ms0 : machine_state) (md0 : Model) : Prop :=
  kbase SK B cx /\
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms0) md0 k2 /\
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) /\
  kin_poison B cx fpos k2 ly3 S3 W3 ms0 md0 /\
  kfrom SK B POST (kin_err B).

(* the bytes the phase writes: the cursor, slot 0xb0, F's right redzone *)
Definition kfl_X (cx : kcx) (fpos : Z) (a : Z) : Prop :=
  (ka0 cx <= a < ka0 cx + 16) \/ (ksp1 cx + 0xb0 <= a < ksp1 cx + 0xb8) \/
  (kFSH cx fpos + 0x428 <= a < kFSH cx fpos + 0x448).

(* the memory of a state of the phase against the cut's *)
Definition kfl_mem (cx : kcx) (fpos : Z) (W3 : world SEGS) (ms0 ms : machine_state) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ kfl_X cx fpos a ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms0) a) /\
  mem_grows (rdW W3 (ms_mem ms0)) (rdW W3 (ms_mem ms)).
Definition kfl_f3 (cx : kcx) (fpos : Z) (W3 : world SEGS) (ms : machine_state) : Prop :=
  forall i, 0x428 <= i < 0x448 -> aview SEGS (w_H W3) (ms_mem ms) (kFSH cx fpos + i) = Some 0xf3.

(* a byte of application memory below 2 ^ 47 *)
Definition kfl_app (x : Z) : Prop := 0 <= x /\ (x < kLowMemEnd \/ (kHighMemBeg <= x /\ x < 2 ^ 47)).

Lemma kfl_akb_app : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi x,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  akb SEGS B lyc Sc slo shi x -> kfl_app x.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi x HJ Hb.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (ajournal_gx_row SK SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
    as (Hlo & Hhi & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  unfold kfl_app.
  destruct Hb as [(H1 & _) | [(b & m & Hin & Hr) | [(Hi & _ & _) | (c & p & Hin & Hr)]]].
  - unfold kHighMemBeg, kLowMemEnd in *. lia.
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & _ & _ & Hia & _).
    pose proof (in_app_addr _ _ x Hia ltac:(lia)) as Hap.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, kLowMemEnd, ASAN_CEIL in *. lia.
  - pose proof (pa_segs_low x Hi). unfold kLowMemEnd in *. lia.
  - destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c p HAR Hin) as (_ & _ & Happ).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hap.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, kLowMemEnd, ASAN_CEIL in *. lia.
Qed.

Lemma kfl_akb_notF : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi x
    S1 W1 mem1 md1 fpos,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B lyc S1 W1 mem1 md1 -> frames S1 = (KN_CID, fpos) :: frames Sc ->
  ablocks B lyc S1 = ablocks B lyc Sc ->
  akb SEGS B lyc Sc slo shi x ->
  ~ (frame_addr lyc KN_CID fpos <= x < frame_addr lyc KN_CID fpos + fs_frame_bytes KN_CID).
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi x S1 W1 mem1 md1 fpos
    HJ HAR1 Hfrs1 Eab1 Hb Hx.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (ajournal_gx_row SK SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
    as (Hlo & Hhi & _).
  assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS lyc S1 W1 mem1 md1 KN_CID fpos HAR1 Hin1) as (Hf4 & Hfc & _).
  destruct Hb as [(H1 & _) | [(b & m & Hin & Hr) | [(Hi & _ & _) | (c & p & Hin & Hr)]]].
  - lia.
  - assert (Hb1 : In (b, m) (ablocks B lyc S1)) by (rewrite Eab1; exact Hin).
    pose proof (sep_block_frame SEGS B LAWS lyc S1 W1 mem1 md1 b m KN_CID fpos HAR1 Hb1 Hin1) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - exact (frm_img SEGS B LAWS lyc S1 W1 mem1 md1 KN_CID fpos x HAR1 Hin1 Hx Hi).
  - apply in_split in Hin as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS lyc S1 W1 mem1 md1 (KN_CID, fpos) (c, p) [] l2 l3 HAR1
      ltac:(rewrite Hfrs1, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng, in_zr in Hd, Hr. cbn [fst snd] in Hd, Hr. lia.
Qed.

(* ---- small facts ---- *)
Lemma kfl_U : forall (w : word) z, w = w64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned w = z.
Proof. intros w z -> Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Lemma kfl_ms_shape : forall (ms : machine_state) pc, kms pc ms ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + kpc pc)) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros [rg fr pcv sv rv fc mm rm] pc (H1 & H2 & H3 & H4 & H5 & H6).
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr] in H1, H2, H3, H4, H5, H6. subst. reflexivity.
Qed.

Lemma kfl_u64_same : forall H (m : word -> option byte) a v v',
  val_mem SEGS (mrestrict H m) a 8 v -> val_mem SEGS (mrestrict H m) a 8 v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
  intros H m a v v' H1 H2 R1 R2.
  pose proof (rdword_of_val_mem SEGS H m a v H1 R1) as E1.
  pose proof (rdword_of_val_mem SEGS H m a v' H2 R2) as E2. congruence.
Qed.

(* the cursor and the input, as kernel_apre states them, at the context's wp / wn *)
Lemma kfl_input_pre : forall cx, kbase SK B cx ->
  amem_range (k_wp cx) (k_wn cx) /\ range_addressable (ard SEGS (km0 cx)) SHADOW_OFF (k_wp cx) (k_wn cx) /\
  kernel_apart (k_regs cx) (k_wp cx) (k_wn cx).
Proof.
  intros cx HB. unfold kbase in HB.
  destruct HB as (_ & _ & HKP & _ & _ & HWP & HWN & HWPr & HWNr & _).
  destruct HKP as (kbs & _ & _ & _ & _ & (wp & wn & HWP' & HWN' & HWPr' & HWNr' & _ & HAMR & HRA & _ & HAP) & _).
  assert (Ep : wp = k_wp cx) by (eapply kfl_u64_same; [exact HWP' | exact HWP | lia | lia]).
  assert (En : wn = k_wn cx) by (eapply kfl_u64_same; [exact HWN' | exact HWN | lia | lia]).
  subst wp wn. split; [exact HAMR | split; [exact HRA | exact HAP]].
Qed.

(* the write set *)
Lemma kfl_apart_notE : forall cx a n x, kernel_apart (k_regs cx) a n -> a <= x < a + n -> ~ kE cx x.
Proof.
  intros cx a n x (_ & Hg & Hl & Hc) Hx HE. unfold kE, inFP in HE. destruct HE as (r & Hin & Hr).
  unfold kernel_awr in Hin. cbn [In] in Hin.
  unfold apart_gnl, apart, LA_G_NL, LA_LONG_ALIAS, LONG_ALIAS_SIZE, NK_CHUNK, NK_OPEN, NK_SIZE in *.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
Qed.

Lemma kfl_kE_cursor : forall cx x, ka0 cx <= x < ka0 cx + 16 -> kE cx x.
Proof.
  intros cx x Hx. unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
  split; [unfold kernel_awr; right; right; left; reflexivity | cbn [fst snd]; unfold ka0 in Hx; lia].
Qed.

(* what the call keeps up to the cut, without F's bytes (LinkWalkSide.v akept_drop_side) *)
Lemma kfl_kept0 : forall POST cx fpos k2 ly3 S3 W3 ms0 md0, kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  akept SEGS B (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) W3 (ms_mem ms0) (ksp cx - KERNEL_AK) (ksp cx) (kE cx).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 (_ & _ & _ & HI & _).
  unfold kin_poison, kat in HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & Hkjb & Hkkp & _).
  destruct Hkjb as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hab1) & _).
  destruct Hkkp as (HK & _).
  exact (akept_drop_side SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ S1 W1 mem1 md1 KN_CID fpos HAR1 Hfrs1 Hab1 HK).
Qed.

(* a byte of the read set outside the write set is, at the cut, the call's *)
Lemma kfl_rd0 : forall POST cx fpos k2 ly3 S3 W3 ms0 md0, kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a -> ~ kE cx a ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H (k_W cx)) (k_memc cx) a.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 HC a Ha HnE.
  pose proof (kfl_kept0 _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct HC as (HB & _). pose proof HB as (HPRE & HRD & _). pose proof HPRE as (HJc & _).
  eapply (akept_akb_gx SK); [exact HJc | exact HK | exact (HRD a Ha) | exact HnE].
Qed.

(* the numbers of the context *)
Lemma kfl_nums : forall POST cx fpos k2 ly3 S3 W3 ms0 md0,
  kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  alloc_ceiling + KERNEL_AK <= ksp cx /\ ksp cx <= 2 ^ 47 /\
  ksp cx - 384 < ksp1 cx /\ ksp1 cx <= ksp cx - 352 /\ ksp1 cx mod 32 = 0 /\
  k_sp0 cx - k_STK cx <= ksp cx - KERNEL_AK /\ ksp cx <= k_sp0 cx /\
  4096 <= kF cx fpos /\ kF cx fpos + 16384 <= alloc_ceiling /\ kF cx fpos mod 64 = 0 /\
  kFSH cx fpos = SHADOW_OFF + kF cx fpos / 8 /\
  0 <= ka0 cx /\ (ka0 cx + 16 <= kLowMemEnd \/ (kHighMemBeg <= ka0 cx /\ ka0 cx + 16 <= 2 ^ 47)) /\
  (ka0 cx + 16 <= ksp cx - KERNEL_AK \/ ksp cx <= ka0 cx) /\
  0 <= k_wp cx /\ k_wp cx + k_wn cx <= 2 ^ 47 - 1 /\ 0 <= k_wn cx /\
  (kF cx fpos + 16384 <= kLowShadowBeg \/ kHighMemBeg <= kF cx fpos) /\
  (ka0 cx + 16 <= kF cx fpos \/ kF cx fpos + 16384 <= ka0 cx).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 HC.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct HC as (HB & HJ3 & HFR & HI & _).
  pose proof (kfl_input_pre cx HB) as (HAMR & _ & _).
  pose proof HB as (HPRE & HRD & HKP & HNK & HWF & HWP & HWN & HWPr & HWNr & _).
  pose proof HPRE as (HJc & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & _).
  destruct (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Hlo & Hhi & Hl1 & Hl2).
  pose proof HJc as (_ & HXO & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & HAPFc & _).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  assert (Hsp : 0 <= ksp cx < 2 ^ 64) by (unfold ksp, spZ; apply getr_rng).
  assert (Ha0r : 0 <= ka0 cx < 2 ^ 64) by (unfold ka0, aarg, argZ; apply getr_rng).
  assert (A0 : kfl_app (ka0 cx)).
  { eapply kfl_akb_app; [exact HJc | apply HRD; unfold kernel_ard; left; unfold ka0 in *; lia]. }
  assert (A15 : kfl_app (ka0 cx + 15)).
  { eapply kfl_akb_app; [exact HJc | apply HRD; unfold kernel_ard; left; unfold ka0 in *; lia]. }
  unfold kin_poison, kat in HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & Hkjb & _).
  destruct Hkjb as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hab1) & _).
  assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 Hin1) as (HF4 & HFc & HFapp).
  destruct (frame_al64 _ _ _ _ _ _ _ _ _ HAR1 Hin1) as (HF64 & _).
  assert (Hfs : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (NF0 : ~ (frame_addr (k_lyc cx) KN_CID fpos <= ka0 cx <
                   frame_addr (k_lyc cx) KN_CID fpos + fs_frame_bytes KN_CID)).
  { eapply kfl_akb_notF; [exact HJc | exact HAR1 | exact Hfrs1 | exact Hab1 |].
    apply HRD. unfold kernel_ard. left. unfold ka0 in *. lia. }
  assert (NF15 : ~ (frame_addr (k_lyc cx) KN_CID fpos <= ka0 cx + 15 <
                    frame_addr (k_lyc cx) KN_CID fpos + fs_frame_bytes KN_CID)).
  { eapply kfl_akb_notF; [exact HJc | exact HAR1 | exact Hfrs1 | exact Hab1 |].
    apply HRD. unfold kernel_ard. left. unfold ka0 in *. lia. }
  rewrite Hfs in HFc, HFapp, NF0, NF15. unfold in_app in HFapp.
  unfold ksp in *.
  destruct (sp1_facts (spZ (k_regs cx) - 352) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
    as (Hs1 & Hs2 & _).
  unfold kfl_app, amem_range, apart_frame in *. unfold ksp1, ksp1_of, KN_MFRAME, ksp.
  unfold kF, kFSH, shadow_of_addr. unfold kF in *.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *. unfold ka0 in *.
  repeat split; lia.
Qed.

(* ---- the shadow byte of a read-set byte, from the call to a later state (LinkWalkShadow.v sbyte_transport,
   without its shadow-group half: kernel_apre gives the cursor's and nl_errno.e's range_addressable but not their
   hull) ---- *)
Lemma kfl_saddr_tr : forall lyc Sc (W : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 slo shi
    (E : Z -> Prop) x,
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B ly2 S2 W2 mem2 md2 ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  akept SEGS B lyc Sc W memc W2 mem2 slo shi E ->
  (forall s, kLowMemEnd <= s < kHighMemBeg -> ~ E s) ->
  akb SEGS B lyc Sc slo shi x ->
  saddr (aview SEGS (w_H W) memc) x -> saddr (aview SEGS (w_H W2) mem2) x.
Proof.
  intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E x HAR1 HAR2 Elo Ehi Hbl HK HE Hb Hs1.
  pose proof HAR1 as (M1 & _). pose proof HAR2 as (M2 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct Hb as [(Hst & _) | [(b & m & Hin & Hb) | [(Hi & _ & _) | (c & q & Hin & Hf)]]].
  - (* the real stack: zero at every AR state *)
    pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly2 S2 _ M2) (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2)
      ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
    cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
    pose proof (am_layout B ly2 S2 _ M2) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Pl & Ph & _).
    unfold page_aligned in Pl, Ph. rewrite Elo, Ehi in *.
    exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
    apply HZ. lia.
  - (* a heap block still alive *)
    pose proof (Hbl b m Hin) as Hin2.
    destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin2) as [HBS _].
    exact (block_shadow_range _ _ _ _ x 1 HBS ltac:(lia) ltac:(lia) x ltac:(lia)).
  - (* the image *)
    pose proof (pa_img_range x Hi) as Hi'. rewrite img_end_val in Hi'.
    assert (Hsx : SHADOW_OFF + 0x2000 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 0xca800)
      by (unfold shadow_of_addr; lia).
    assert (Eq : aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF x) =
                 aview SEGS (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
    { eapply proj1. eapply img_sh_eq; eauto. }
    destruct Hs1 as (v & Hv & Hok). exists v. rewrite Eq. split; [exact Hv | exact Hok].
  - (* a side frame of the call *)
    pose proof HK as (_ & _ & _ & K4 & _).
    destruct (frame_facts B lyc Sc _ c q M1 Hin) as (_ & _ & Happ & _ & PF & _ & _ & Hoff & H64 & Hb64 & _).
    unfold page_aligned in PF. unfold in_app, kFakeStackSize in Happ.
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c q HAR1 Hin) as (Hf4096 & Hfceil & _).
    assert (HF64 : frame_addr lyc c q mod 64 = 0) by (unfold frame_addr; lia).
    unfold in_zr, frame_rng in Hf. cbn [fst snd] in Hf.
    assert (KS : forall s, shadow_addr x / 8 * 8 <= s < shadow_addr x / 8 * 8 + 8 ->
      aview SEGS (w_H W2) mem2 s = aview SEGS (w_H W) memc s).
    { intros s Hs.
      assert (Hsf : shadow_addr (frame_addr lyc c q) <= s < shadow_addr (frame_addr lyc c q) + fs_frame_bytes c / 8)
        by (unfold shadow_addr, SHADOW_OFF in *; lia).
      apply (K4 c q s Hin).
      - right. unfold in_zr. cbn [fst snd]. exact Hsf.
      - apply HE. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. lia. }
    destruct Hs1 as (v & Hv & Hok). exists v. split; [|exact Hok].
    rewrite (KS (shadow_of_addr SHADOW_OFF x)); [exact Hv|]. unfold shadow_of_addr, shadow_addr, SHADOW_OFF. lia.
Qed.

(* the shadow byte of a read-set byte at the cut is usable as it was at the call *)
Lemma kfl_sh0 : forall POST cx fpos k2 ly3 S3 W3 ms0 md0, kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  forall x, kernel_ard SEGS (k_regs cx) (km0 cx) x -> saddr (aview SEGS (w_H (k_W cx)) (k_memc cx)) x ->
  saddr (aview SEGS (w_H W3) (ms_mem ms0)) x.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 HC x Hx Hs.
  pose proof (kfl_kept0 _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ha0 & Ha0r & _).
  destruct HC as (HB & HJ3 & HFR & HI & _).
  pose proof HB as (HPRE & HRD & _). pose proof HPRE as (HJc & _).
  pose proof HJc as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR1 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR2 & _).
  assert (Rc : ly_stk_lo (k_lyc cx) = ly_stk_lo (k_ly cx) /\ ly_stk_hi (k_lyc cx) = ly_stk_hi (k_ly cx))
    by (eapply aj_stk_row_eq; eauto).
  assert (R3 : ly_stk_lo ly3 = ly_stk_lo (k_ly cx) /\ ly_stk_hi ly3 = ly_stk_hi (k_ly cx))
    by (eapply aj_stk_row_eq; eauto).
  unfold kin_poison, kat in HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & Hkjb & _).
  destruct Hkjb as (_ & _ & HPerm & _).
  eapply kfl_saddr_tr; [exact HAR1 | exact HAR2 | lia | lia | | exact HK | | exact (HRD x Hx) | exact Hs].
  - intros b m Hin. exact (Permutation_in _ (Permutation_sym HPerm) Hin).
  - intros s Hs' HE. unfold kE, inFP in HE. destruct HE as (r & Hin & Hr).
    unfold kernel_awr in Hin. cbn [In] in Hin.
    unfold LA_G_NL, LA_LONG_ALIAS, LONG_ALIAS_SIZE, NK_CHUNK, NK_OPEN, kLowMemEnd, kHighMemBeg in *.
    unfold ka0 in Ha0r.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
Qed.

(* the cursor's, nl_errno.e's and the input's shadow at the cut *)
Lemma kfl_ra0 : forall POST cx fpos k2 ly3 S3 W3 ms0 md0, kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (ka0 cx) 16 /\
  range_addressable (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF LA_NL_ERRNO_E 24 /\
  range_addressable (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (k_wp cx) (k_wn cx).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 HC.
  pose proof (kfl_sh0 _ _ _ _ _ _ _ _ _ HC) as SH.
  destruct HC as (HB & _).
  pose proof (kfl_input_pre cx HB) as (_ & HRAw & _).
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (_ & _ & HKP & _ & _ & HWP & HWN & HWPr & HWNr & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & HRAc & _ & _ & _ & _ & HRAe & _).
  split; [|split]; intros x Hx; apply SH.
  - unfold kernel_ard. left. unfold ka0 in Hx. lia.
  - exact (HRAc x Hx).
  - unfold kernel_ard. right; right; right; left. exact Hx.
  - exact (HRAe x Hx).
  - unfold kernel_ard. right; left. exists (k_wp cx), (k_wn cx). unfold ka0 in HWP, HWN. auto.
  - exact (HRAw x Hx).
Qed.

(* nl_errno.e's six words at the cut *)
Lemma kfl_nlerr0 : forall POST cx fpos k2 ly3 S3 W3 ms0 md0, kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  forall off v, In (off, v) [(0, 105); (4, 4); (8, 11); (12, 1); (16, 24); (20, 111)] ->
  val_mem SEGS (rdW W3 (ms_mem ms0)) (0x21080 + off) 4 v.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 HC off v Hin.
  pose proof (kfl_rd0 _ _ _ _ _ _ _ _ _ HC) as RD.
  destruct HC as (HB & _). pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (_ & _ & HKP & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNL & HRAe & HAPe & _).
  assert (Hi : exists i, 0 <= i < 6 /\ off = 4 * i /\ v = nth (Z.to_nat i) nl_errno_tab 0).
  { cbn [In] in Hin.
    destruct Hin as [E | [E | [E | [E | [E | [E | []]]]]]]; injection E as <- <-;
      [exists 0 | exists 1 | exists 2 | exists 3 | exists 4 | exists 5]; (split; [lia | split; [lia | reflexivity]]). }
  destruct Hi as (i & Hi & -> & ->).
  pose proof (HNL i Hi) as Hv.
  eapply vm_frame; [| exact Hv].
  intros x Hx. apply (mbyte_of_aview SEGS). apply RD.
  - unfold kernel_ard. right; right; right; left. unfold LA_NL_ERRNO_E in *. cbn [Z.of_nat] in Hx. lia.
  - apply (kfl_apart_notE cx _ _ x HAPe). unfold LA_NL_ERRNO_E in *. cbn [Z.of_nat] in Hx. lia.
Qed.

(* ==========================================================================
   THE START: the symbolic state at +0x194 from the cut kin_poison
   ========================================================================== *)
Lemma kfl_start : forall POST cx fpos k2 ly3 S3 W3 ms0 md0, kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  st_ok_pi SEGS pa_val (kfl_E0 cx W3 ms0) kfl_ss0 (restrict (w_H W3) ms0).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 HC.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & Hs1m & Hwlo & Hwhi & HF4 & HFc & HF64 &
    HFSH & Ha0 & Ha0r & Hapf & Hwp0 & Hwpn & Hwn0 & HFapp & HFa0).
  pose proof (kfl_nlerr0 _ _ _ _ _ _ _ _ _ HC) as HNE.
  destruct HC as (HB & HJ3 & HFR & HI & _).
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (_ & _ & HKP & _ & _ & _ & _ & HWPr & HWNr & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAPe & _).
  unfold kin_poison, kat in HI.
  destruct HI as (Hkms & Hkr0 & Hkrl & Hksv & Hkfr & Hksh & Hksl & Hkjb & Hkkp & Hkcu & Hkg & Hkla).
  destruct Hkr0 as (Hr2 & Hr9 & Hr8 & Hr3 & Hr4 & Hr18 & Hr20).
  destruct (kfl_forall3 _ _ _ _ Hkrl) as (_ & _ & Hr22). cbn [fst snd] in Hr22.
  destruct Hkcu as (Hadv & Hcp & Hcn & Hcw).
  destruct Hkfr as (_ & _ & _ & _ & _ & Hfsp).
  assert (Hfs : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  rewrite Hfs in Hfsp. unfold SHADOW_OFF in HFSH.
  assert (HFSHr : 0 <= kFSH cx fpos < 2 ^ 64) by (rewrite HFSH; lia).
  assert (Hs1r : 0 <= ksp1 cx < 2 ^ 64) by lia.
  set (E := kfl_E0 cx W3 ms0).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms0) r)
    by (intros n r Hn; unfold E, kfl_E0; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (EX : forall j, (j < 11)%nat -> ew E (32 + j) = nth j (kfl_ext cx W3 ms0) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, kfl_E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E256 : ew E (A_OBJ 15) = Z_to_bv 64 0x21080).
  { unfold E, kfl_E0. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj LV) by (vm_compute; lia). reflexivity. }
  assert (U9 : bv_unsigned (ew E 9) = ksp1 cx) by (rewrite (ER 9%nat 9%bv eq_refl); apply kfl_U; [exact Hr9 | lia]).
  assert (U18 : bv_unsigned (ew E 18) = ka0 cx)
    by (rewrite (ER 18%nat 18%bv eq_refl); apply kfl_U; [exact Hr18 | lia]).
  assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
    by (rewrite (ER 20%nat 20%bv eq_refl); apply kfl_U; [exact Hr20 | unfold SHADOW_OFF; lia]).
  assert (U22 : bv_unsigned (ew E 22) = kFSH cx fpos)
    by (rewrite (ER 22%nat (Z_to_bv 5 (Z.of_nat 22)) ltac:(vm_compute; reflexivity)); apply kfl_U; [exact Hr22 | lia]).
  assert (E32 : ew E 32 = Z_to_bv 64 (k_wp cx)) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = Z_to_bv 64 (k_wn cx)) by exact (EX 1%nat ltac:(lia)).
  assert (U32 : bv_unsigned (ew E 32) = k_wp cx) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = k_wn cx) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U256 : bv_unsigned (ew E (A_OBJ 15)) = 0x21080) by (rewrite E256; apply unsigned_lit_small; lia).
  rewrite (kfl_ms_shape ms0 KP_POISON Hkms). rewrite restrict_mkst_fx. unfold kfl_ss0.
  apply pa_entry_st_ok_full.
  - unfold E, kfl_E0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold kfl_rF, kfl_rS, kfl_rC.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U22. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (kn_apresent_writable SEGS). apply Hfsp. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (kn_apresent_writable SEGS).
      apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3). lia.
    + rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) (k_wp cx)).
        -- apply sv_off0. exact E32.
        -- change (8 * Z.of_N 8) with 64. lia.
        -- cbn. lia.
        -- rewrite Z.add_0_r. rewrite Z.add_0_r in Hcp. exact Hcp.
      * apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SOff 33 0) (k_wn cx)).
        -- apply sv_off0. exact E33.
        -- change (8 * Z.of_N 8) with 64. lia.
        -- cbn. lia.
        -- rewrite Z.sub_0_r in Hcn. exact Hcn.
  - apply pairwise_disjoint_of_extents.
    unfold kfl_rF, kfl_rS, kfl_rC, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U22, U9, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct HAPe as (_ & _ & _ & HAPc). unfold apart, LA_NL_ERRNO_E in HAPc.
    rewrite HFSH. unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. unfold ka0 in *.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    unfold kfl_facts0. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U9, U18, U22, U32, U33, U256.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    rewrite HFSH. unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* ==========================================================================
   THE PHASE'S STATES: any state of the phase (kfl_mid) and a cut of it (kfl_at)
   ========================================================================== *)
Definition kfl_Y (cx : kcx) (a : Z) : Prop :=
  (ka0 cx <= a < ka0 cx + 16) \/ (ksp1 cx + 0xb0 <= a < ksp1 cx + 0xb8).

Definition kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 (ms : machine_state) (md : Model) : Prop :=
  kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 /\
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 /\
  m_fds md = m_fds md0 /\ m_fs md = m_fs md0 /\
  kfl_mem cx fpos W3 ms0 ms /\ kfl_f3 cx fpos W3 ms.

Definition kfl_base_regs (cx : kcx) (fpos : Z) : list (nat * Z) :=
  [(19%nat, kF cx fpos); (21%nat, kF cx fpos); (22%nat, kFSH cx fpos); (24%nat, kS8 cx);
   (11%nat, ka0 cx / 8); (12%nat, LA_NL_ERRNO_E)].
Definition kfl_k0 (cx : kcx) : list (nat * Z) :=
  [(2%nat, ksp1 cx); (9%nat, ksp1 cx); (8%nat, ksp cx); (18%nat, ka0 cx); (20%nat, SHADOW_OFF)].

Definition kfl_at POST cx fpos k2 ly3 S3 W3 ms0 md0 (pc adv : Z) (rl : list (nat * Z)) (ms : machine_state)
  (md : Model) : Prop :=
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md /\
  kms pc ms /\ kregs0 cx ms /\ kregs_eq ms (kfl_base_regs cx fpos ++ rl) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (ksp1 cx + KS_CN) = Some (ka0 cx + 8) /\
  0 <= adv <= k_wn cx /\
  au64_at SEGS (rdW W3 (ms_mem ms)) (ka0 cx) (k_wp cx + adv) /\
  au64_at SEGS (rdW W3 (ms_mem ms)) (ka0 cx + 8) (k_wn cx - adv).

Lemma kfl_notX : forall cx fpos a,
  (a < ka0 cx \/ ka0 cx + 16 <= a) -> (a < ksp1 cx + 0xb0 \/ ksp1 cx + 0xb8 <= a) ->
  (a < kFSH cx fpos + 0x428 \/ kFSH cx fpos + 0x448 <= a) -> ~ kfl_X cx fpos a.
Proof. intros cx fpos a H1 H2 H3 HX. unfold kfl_X in HX. lia. Qed.

(* F's shadow is outside the cursor and the slot *)
Lemma kfl_FSH_Y : forall POST cx fpos k2 ly3 S3 W3 ms0 md0, kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  forall a, kFSH cx fpos <= a < kFSH cx fpos + 2048 -> ~ kfl_Y cx a /\ 0 <= a < 2 ^ 64.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 HC a Ha.
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (Hsp & _ & Hs1a & _ & _ & _ & _ & HF4 & HFc & _ & HFSH & Ha0 & Ha0r & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  rewrite C3, C5 in Ha0r. rewrite HFSH in Ha. unfold kfl_Y. unfold SHADOW_OFF in Ha. lia.
Qed.

(* a step of the phase (a run whose writable windows lie in the cursor and the slot) keeps kfl_mid *)
Lemma kfl_mid_step : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md ms' md' E rs,
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  frame_of E rs (rdW W3 (ms_mem ms)) (rdW W3 (ms_mem ms')) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> kfl_Y cx a) ->
  mem_grows (rdW W3 (ms_mem ms)) (rdW W3 (ms_mem ms')) ->
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms' md'.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md ms' md' E rs (HC & _ & Hfds & Hfs & (HM1 & HM2) & HF3)
    HJ' Hfds' Hfs' HFr Hw HG.
  pose proof (kept_of_frame (segs := SEGS) E rs (w_H W3) (ms_mem ms) (ms_mem ms') (kfl_Y cx) HFr Hw) as KY.
  split; [exact HC|]. split; [exact HJ'|]. split; [congruence|]. split; [congruence|]. split.
  - split.
    + intros a Ha Hn. rewrite (KY a Ha) by (unfold kfl_X, kfl_Y in *; tauto). exact (HM1 a Ha Hn).
    + exact (mem_grows_trans _ _ _ HM2 HG).
  - intros i Hi. destruct (kfl_FSH_Y _ _ _ _ _ _ _ _ _ HC (kFSH cx fpos + i) ltac:(lia)) as (Hy & Hr).
    rewrite (KY _ Hr Hy). exact (HF3 i Hi).
Qed.

(* the journal admits the phase's writes: the cursor (kernel's write set), the slot (its window), F's shadow *)
Lemma kfl_awr : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 E rs,
  kfl_C POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  (forall a, in_wrange E rs a -> kfl_X cx fpos a) ->
  awr_ok_x E rs (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 E rs HC HX a Ha.
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & _ & Hwlo & Hwhi & HF4 & HFc & _ & HFSH & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  pose proof HC as (HB & HJ3 & HFR & HI & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWR & _).
  assert (FA : forall c q, frame_addr ly3 c q = frame_addr (k_lyc cx) c q).
  { intros c q. rewrite (aj_frame_addr SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 c q).
    rewrite (aj_frame_addr SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc c q). reflexivity. }
  destruct (HX a Ha) as [Hc | [Hs | Hf]].
  - pose proof (HWR a (kfl_kE_cursor cx a Hc)) as Hw.
    unfold kin_poison, kat in HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & HPerm & _) & _).
    exact (ajw_mono B _ _ _ _ _ _ _ _ _ _ _ ly3 S3 ((KN_CID, fpos) :: k_own cx) a Hw
      (fun b m Hin => Permutation_in _ (Permutation_sym HPerm) Hin) (fun x Hx => or_intror Hx) FA).
  - left. split; [left; lia | lia].
  - left. split.
    + right; right; right. exists KN_CID, fpos. split; [left; reflexivity|]. right.
      unfold in_zr, shadow_addr. cbn [fst snd]. rewrite FA.
      assert (Hfs : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfs.
      unfold kFSH, kF, shadow_of_addr in Hf. lia.
    + unfold SHADOW_OFF in HFSH. lia.
Qed.

(* a region of a state, by membership *)
Lemma kfl_region_in : forall E ss ms r, st_ok_pi SEGS pa_val E ss ms -> In r (ss_mem ss) ->
  region_ok SEGS E (ms_mem ms) r.
Proof.
  intros E ss ms r HS Hin. destruct (In_nth_error _ _ Hin) as (i & Hi).
  exact (st_ok_pi_region_nth E ss ms i r HS Hi).
Qed.

(* THE EXIT: a cut of the phase from a symbolic state the run reached *)
Lemma kfl_exit : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl E ss ms md,
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md ->
  st_ok_pi SEGS pa_val E ss (restrict (w_H W3) ms) ->
  ss_pc ss = kpc pc -> ss_resv ss = None ->
  kfl_regsP E ss (kfl_k0 cx ++ kfl_base_regs cx fpos ++ rl) ->
  sv_denot E (sr_get (ss_regs ss) 3) = getr (k_regs cx) 3 ->
  sv_denot E (sr_get (ss_regs ss) 4) = getr (k_regs cx) 4 ->
  In kfl_rS1 (ss_mem ss) -> In (kfl_rCa adv) (ss_mem ss) ->
  ew E 9 = w64 (ksp1 cx) -> ew E 18 = w64 (ka0 cx) -> ew E 32 = w64 (k_wp cx) -> ew E 33 = w64 (k_wn cx) ->
  0 <= adv <= k_wn cx ->
  kfl_at POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl E ss ms md HM HS Hpc Hrv HR HR3 HR4 HinS HinC
    E9 E18 E32 E33 Hadv.
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ (proj1 HM)) as (Hsp & Hsp47 & Hs1a & Hs1b & _ & _ & _ & _ & _ & _ & _ &
    Ha0 & Ha0r & _ & Hwp0 & Hwpn & Hwn0 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  rewrite C3, C5 in Ha0r.
  pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hsh. rewrite Hpc in Hsh.
  destruct (ms_shape_mkst SEGS ms _ _ _ Hsh) as (Q2 & Q3 & Q4 & Q5 & Q6 & Q1).
  assert (RGs : forall r v, In (r, v) (kfl_k0 cx ++ kfl_base_regs cx fpos ++ rl) ->
                 sv_denot E (sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat r))) = w64 v).
  { intros r v Hin. unfold kfl_regsP in HR. rewrite Forall_forall in HR. exact (HR (r, v) Hin). }
  assert (RG : forall r v, In (r, v) (kfl_k0 cx ++ kfl_base_regs cx fpos ++ rl) ->
                 getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = w64 v).
  { intros r v Hin. rewrite (st_ok_pi_restrict_reg (w_H W3) E ss ms _ HS). exact (RGs r v Hin). }
  assert (U9 : bv_unsigned (ew E 9) = ksp1 cx) by (rewrite E9; apply kfl_U; [reflexivity | lia]).
  assert (U18 : bv_unsigned (ew E 18) = ka0 cx) by (rewrite E18; apply kfl_U; [reflexivity | lia]).
  pose proof (kfl_region_in E ss _ _ HS HinS) as HRS. cbn [ms_mem restrict] in HRS.
  pose proof (kfl_region_in E ss _ _ HS HinC) as HRC. cbn [ms_mem restrict] in HRC.
  unfold kfl_at. split; [exact HM|].
  split; [exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 Q6)))))|].
  split.
  { unfold kregs0.
    repeat match goal with |- _ /\ _ => split end;
      lazymatch goal with |- getr _ ?b = _ => rewrite (st_ok_pi_restrict_reg (w_H W3) E ss ms b HS) end;
      first [ exact HR3 | exact HR4
            | lazymatch goal with |- sv_denot _ (sr_get _ ?b) = w64 ?v =>
                let n := eval vm_compute in (Z.to_nat (bv_unsigned b)) in
                transitivity (sv_denot E (sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat n)))); [reflexivity|];
                apply (RGs n v); cbn [kfl_k0 app In]; repeat (first [left; reflexivity | right]) end ]. }
  split.
  { unfold kregs_eq. rewrite Forall_forall. intros (r & v) Hin. apply RG. apply in_or_app. right. exact Hin. }
  split.
  { apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms) (ksp1 cx + KS_CN) (ka0 cx + 8)); [|lia].
    exact (field_of_region (segs := SEGS) E _ 9 (ksp1 cx) _ _ _ _ _ 0xb0 8 (SOff 18 8) (ka0 cx + 8) HRS U9
      ltac:(cbn; left; reflexivity) (kfl_den_off E 18 (ka0 cx) 8 E18 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)). }
  split; [exact Hadv|].
  split.
  { pose proof (field_of_region (segs := SEGS) E _ 18 (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 adv) (k_wp cx + adv) HRC U18
      ltac:(cbn; left; reflexivity) (kfl_den_off E 32 (k_wp cx) adv E32 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia))
      as Hv.
    rewrite Z.add_0_r in Hv. exact Hv. }
  { refine (field_of_region (segs := SEGS) E _ 18 (ka0 cx) _ _ _ _ _ 8 8 (SOff 33 (- adv)) (k_wn cx - adv) HRC U18
      ltac:(cbn; right; left; reflexivity) _ ltac:(cbn; lia) ltac:(cbn; lia)).
    rewrite (kfl_den_off E 33 (k_wn cx) (- adv) E33 ltac:(lia)). f_equal; lia. }
Qed.

(* THE END: kin_err from a cut of the phase at +0x3b4 *)
Lemma kfl_fin : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 adv fl e ei ms md,
  kfl_at POST cx fpos k2 ly3 S3 W3 ms0 md0 KP_ERR adv [(10%nat, ei); (13%nat, fl); (15%nat, e)] ms md ->
  0 <= fl < 256 -> In e nl_errno_tab -> 0 <= ei < 6 -> adv <= 3 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 adv fl e ei ms md HA Hfl He Hei Hadv3.
  destruct HA as ((HC & HJ & Hfds & Hfs & (UN & HG) & HF3) & Hkms & Hkr0 & Hkre & Hslot & Hadv & Hcp & Hcn).
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & Hs1m & Hwlo & Hwhi & HF4 & HFc & HF64 &
    HFSH & Ha0 & Ha0r & Hapf & Hwp0 & Hwpn & Hwn0 & HFapp & HFa0).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  assert (Hfs16 : fs_frame_bytes KN_CID = 16384) by reflexivity.
  rewrite C3, C5 in Ha0r. rewrite C3 in HFapp. unfold kLowShadowBeg in HFapp. unfold SHADOW_OFF in HFSH.
  pose proof HC as (HB & HJ3 & HFR & HI & HNEXT).
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (_ & _ & HKP & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & _ & Hgc & Hlc & _).
  unfold apart_gnl, apart in Hgc, Hlc. fold (ka0 cx) in Hgc, Hlc.
  unfold kin_poison, kat in HI.
  destruct HI as (_ & _ & _ & Hksv & Hkfr & Hksh & Hksl & Hkjb & Hkkp & Hkcu & Hkg & Hkla).
  assert (HP : forall a, apresent (w_H W3) (ms_mem ms0) a -> apresent (w_H W3) (ms_mem ms) a)
    by (intros a; exact (apresent_grows _ _ _ a HG)).
  apply (HNEXT cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  unfold kin_err. exists fl, e, ei, adv.
  split; [exact Hfl|]. split; [exact He|]. split; [exact Hei|]. split; [exact Hadv3|].
  unfold kat.
  refine (conj Hkms (conj Hkr0 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
  - unfold kregs_eq in Hkre |- *. rewrite Forall_forall in Hkre |- *. intros rv Hin. apply Hkre.
    unfold kfl_base_regs. cbn [app In] in Hin |- *. tauto.
  - refine (ksaved_frame SK B (kfl_X cx fpos) cx W3 ms0 W3 ms HB UN _ Hksv).
    intros a Ha. apply kfl_notX; lia.
  - refine (kframe_frame B LAWS (kfl_X cx fpos) cx fpos true k2 ly3 S3 md0 W3 ms0 W3 ms Hkjb UN HP _ _ Hkfr);
      intros a Ha; rewrite ?Hfs16 in Ha; apply kfl_notX; unfold kF in *; lia.
  - intros i Hi. rewrite kfsh_length in Hi.
    destruct (Nat.lt_ge_cases i 0x428) as [Hlo | Hhi].
    + rewrite (kfl_kfsh_lo i 0xf8 0xf8 0xf3 0 Hlo).
      rewrite UN; [apply Hksh; rewrite kfsh_length; exact Hi | lia | apply kfl_notX; lia].
    + rewrite (kfl_kfsh_hi i 0xf8 0xf8 0xf3 ltac:(lia)). apply HF3. lia.
  - unfold kslots_eq.
    change [(KS_W1SH, kFSH cx fpos + 4); (KS_W2SH, kFSH cx fpos + 0x226); (KS_F2, kF cx fpos); (KS_CN, ka0 cx + 8)]
      with ([(KS_W1SH, kFSH cx fpos + 4); (KS_W2SH, kFSH cx fpos + 0x226); (KS_F2, kF cx fpos)] ++
            [(KS_CN, ka0 cx + 8)]).
    apply Forall_app. split.
    + refine (kslots_frame SK B (kfl_X cx fpos) cx _ _ W3 ms0 W3 ms HB UN (incl_refl _) _ Hksl).
      intros ov Hov. cbn [In] in Hov.
      destruct Hov as [<- | [<- | [<- | []]]]; cbn [fst]; unfold KS_W1SH, KS_W2SH, KS_F2;
        (split; [lia | intros a Ha; apply kfl_notX; lia]).
    + apply Forall_cons; [exact Hslot | apply Forall_nil].
  - exact (kjbk_md B cx fpos k2 ly3 S3 md0 md Hkjb Hfds Hfs).
  - refine (kkept_frame SK B LAWS (kfl_X cx fpos) cx fpos k2 ly3 S3 md0 W3 ms0 W3 ms HB Hkjb UN HP _ Hkkp).
    intros a [Ha | [Ha | Ha]]; unfold kX_in.
    + left. exact (kfl_kE_cursor cx a Ha).
    + right; right; right. lia.
    + right; right; left. rewrite Hfs16. lia.
  - destruct Hkcu as (_ & _ & _ & Hcw).
    refine (conj Hadv (conj Hcp (conj Hcn _))).
    intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (Hcw i Hi)).
  - refine (kgnl_frame (kfl_X cx fpos) cx None W3 ms0 W3 ms UN HP _ Hkg).
    intros a Ha. apply kfl_notX; unfold LA_G_NL, NK_SIZE in *; lia.
  - refine (kla_frame (kfl_X cx fpos) W3 ms0 W3 ms UN HP _ Hkla).
    intros a Ha. apply kfl_notX; unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in *; lia.
Qed.

(* ==========================================================================
   THE BUILD: the symbolic state at a cut of the phase
   ========================================================================== *)
Definition kfl_EM (cx : kcx) (W3 : world SEGS) (ms0 ms : machine_state) : env :=
  Eimg (Ereg (ms_regs ms) (kfl_ext cx W3 ms0)).

Lemma kfl_EM_reg : forall cx W3 ms0 ms (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (kfl_EM cx W3 ms0 ms) n = getr (ms_regs ms) r.
Proof. intros cx W3 ms0 ms n r Hn. unfold kfl_EM. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma kfl_EM_x : forall cx W3 ms0 ms,
  ew (kfl_EM cx W3 ms0 ms) 32 = w64 (k_wp cx) /\ ew (kfl_EM cx W3 ms0 ms) 33 = w64 (k_wn cx) /\
  ew (kfl_EM cx W3 ms0 ms) (A_OBJ 15) = w64 LA_NL_ERRNO_E /\
  (forall j : nat, (j < 3)%nat ->
     ew (kfl_EM cx W3 ms0 ms) (34 + j) = w64 (kfl_q cx (Z.of_nat j)) /\
     ew (kfl_EM cx W3 ms0 ms) (37 + j) = w64 (kfl_s cx W3 ms0 (Z.of_nat j)) /\
     ew (kfl_EM cx W3 ms0 ms) (40 + j) = w64 (kfl_d cx (Z.of_nat j))).
Proof.
  intros cx W3 ms0 ms.
  assert (EX : forall j, (j < 11)%nat -> ew (kfl_EM cx W3 ms0 ms) (32 + j) = nth j (kfl_ext cx W3 ms0) (Z_to_bv 64 0))
    by (intros j Hj; unfold kfl_EM; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  split; [exact (EX 0%nat ltac:(lia))|]. split; [exact (EX 1%nat ltac:(lia))|]. split.
  { unfold kfl_EM. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj LV) by (vm_compute; lia). reflexivity. }
  intros j Hj. destruct j as [|[|[|j]]]; [| | | lia].
  - exact (conj (EX 2%nat ltac:(lia)) (conj (EX 5%nat ltac:(lia)) (EX 8%nat ltac:(lia)))).
  - exact (conj (EX 3%nat ltac:(lia)) (conj (EX 6%nat ltac:(lia)) (EX 9%nat ltac:(lia)))).
  - exact (conj (EX 4%nat ltac:(lia)) (conj (EX 7%nat ltac:(lia)) (EX 10%nat ltac:(lia)))).
Qed.

(* the read-set bytes the phase reads are, at any state of it, as at the cut kin_poison *)
Lemma kfl_UN_ard : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md a,
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md ->
  kernel_ard SEGS (k_regs cx) (km0 cx) a -> ~ (ka0 cx <= a < ka0 cx + 16) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms0) a /\
  aview SEGS (w_H W3) (ms_mem ms) (shadow_of_addr SHADOW_OFF a) =
  aview SEGS (w_H W3) (ms_mem ms0) (shadow_of_addr SHADOW_OFF a).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md a (HC & _ & _ & _ & (UN & _) & _) Hrd Hnc.
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & Hs1m & Hwlo & Hwhi & HF4 & HFc & HF64 &
    HFSH & Ha0 & Ha0r & Hapf & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  rewrite C3, C5 in Ha0r.
  pose proof HC as (HB & _ & _ & HI & _).
  unfold kin_poison, kat in HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & Hkjb & _).
  destruct (kn_ard_bound SK B LAWS cx a HB Hrd) as (Hab & Hnw).
  pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md0 a HB Hkjb Hrd) as HnF.
  pose proof (kfl_akb_app (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx)
    (ksp cx - KERNEL_AK) (ksp cx) a ltac:(destruct HB as ((HJc & _) & _); exact HJc)
    ltac:(destruct HB as (_ & HRD & _); exact (HRD a Hrd))) as Happ.
  unfold kfl_app in Happ. rewrite C3, C5 in Happ.
  assert (Hfs16 : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfs16 in HnF.
  pose proof (kfl_shadow_out (kF cx fpos) a 2048 ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hso.
  split.
  - apply UN; [lia|]. apply kfl_notX; [lia | lia |]. rewrite HFSH. unfold SHADOW_OFF. lia.
  - apply UN; [unfold shadow_of_addr, SHADOW_OFF; lia|].
    apply kfl_notX; unfold shadow_of_addr, SHADOW_OFF in *; [lia | lia |]. rewrite HFSH in *. lia.
Qed.

Lemma kfl_build : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md (withE : bool),
  kfl_at POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md ->
  st_ok_pi SEGS pa_val (kfl_EM cx W3 ms0 ms) (kfl_ssM pc adv (if withE then [kfl_rE] else []))
    (restrict (w_H W3) ms).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md withE HA.
  pose proof HA as (HM & Hkms & Hkr0 & Hkre & Hslot & Hadv & Hcp & Hcn).
  pose proof HM as (HC & HJ & _ & _ & (UN & HG) & _).
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & Hs1m & Hwlo & Hwhi & HF4 & HFc & HF64 &
    HFSH & Ha0 & Ha0r & Hapf & Hwp0 & Hwpn & Hwn0 & _).
  pose proof (kfl_nlerr0 _ _ _ _ _ _ _ _ _ HC) as HNE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  rewrite C3, C5 in Ha0r.
  pose proof HC as (HB & _ & _ & HI & _).
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (_ & _ & HKP & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAPe & _).
  destruct HAPe as (_ & _ & _ & HAPc). unfold apart, LA_NL_ERRNO_E in HAPc. fold (ka0 cx) in HAPc.
  unfold kin_poison, kat in HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hkcu & _).
  destruct Hkcu as (_ & _ & _ & Hcw).
  destruct Hkr0 as (Hr2 & Hr9 & Hr8 & Hr3 & Hr4 & Hr18 & Hr20).
  destruct (kfl_EM_x cx W3 ms0 ms) as (E32 & E33 & E256 & _).
  set (E := kfl_EM cx W3 ms0 ms) in *.
  assert (U9 : bv_unsigned (ew E 9) = ksp1 cx)
    by (unfold E; rewrite (kfl_EM_reg cx W3 ms0 ms 9 9%bv eq_refl); apply kfl_U; [exact Hr9 | lia]).
  assert (U18 : bv_unsigned (ew E 18) = ka0 cx)
    by (unfold E; rewrite (kfl_EM_reg cx W3 ms0 ms 18 18%bv eq_refl); apply kfl_U; [exact Hr18 | lia]).
  assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
    by (unfold E; rewrite (kfl_EM_reg cx W3 ms0 ms 20 20%bv eq_refl); apply kfl_U; [exact Hr20 | unfold SHADOW_OFF; lia]).
  assert (U32 : bv_unsigned (ew E 32) = k_wp cx) by (rewrite E32; apply kfl_U; [reflexivity | lia]).
  assert (U33 : bv_unsigned (ew E 33) = k_wn cx) by (rewrite E33; apply kfl_U; [reflexivity | lia]).
  assert (U256 : bv_unsigned (ew E (A_OBJ 15)) = 0x21080)
    by (rewrite E256; apply kfl_U; [reflexivity | unfold LA_NL_ERRNO_E; lia]).
  assert (RS : region_ok SEGS E (rdW W3 (ms_mem ms)) kfl_rS1).
  { unfold kfl_rS1, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split.
    - intros o Ho. apply (kn_apresent_writable SEGS).
      apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
    - apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (ksp1 cx) 0xb0 8 (SOff 18 8) (ka0 cx + 8)).
      + apply kfl_den_off; [unfold E; rewrite (kfl_EM_reg cx W3 ms0 ms 18 18%bv eq_refl); exact Hr18 | lia].
      + cbn. lia.
      + cbn. lia.
      + exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms) _ _ Hslot). }
  assert (RC : region_ok SEGS E (rdW W3 (ms_mem ms)) (kfl_rCa adv)).
  { unfold kfl_rCa, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
    split; [lia|]. split; [lia|]. split.
    - intros o Ho. exact (writable_at_grows SEGS _ _ _ HG (Hcw o Ho)).
    - constructor; [|constructor; [|constructor]].
      + apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 adv) (k_wp cx + adv)).
        * apply kfl_den_off; [exact E32 | lia].
        * change (8 * Z.of_N 8) with 64. lia.
        * cbn. lia.
        * rewrite Z.add_0_r. exact Hcp.
      + apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SOff 33 (- adv)) (k_wn cx - adv)).
        * rewrite (kfl_den_off E 33 (k_wn cx) (- adv) E33 ltac:(lia)). f_equal; lia.
        * change (8 * Z.of_N 8) with 64. lia.
        * cbn. lia.
        * exact Hcn. }
  assert (RE : region_ok SEGS E (rdW W3 (ms_mem ms)) kfl_rE).
  { unfold kfl_rE, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U256.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons; [eapply (chunk_ok_val SEGS E _ 0x21080 _ 4 _ _);
      [reflexivity | split; [lia | reflexivity] | cbn; lia |
       eapply vm_frame; [|apply HNE; cbn [In]; repeat (first [left; reflexivity | right])];
       intros x Hx; apply (mbyte_of_aview SEGS);
       refine (proj1 (kfl_UN_ard _ _ _ _ _ _ _ _ _ _ _ x HM _ _));
       [unfold kernel_ard; right; right; right; left; unfold LA_NL_ERRNO_E; cbn in Hx; lia
       | unfold LA_NL_ERRNO_E in *; cbn in Hx; lia]] |]).
    apply Forall_nil. }
  rewrite (kfl_ms_shape ms pc Hkms).
  rewrite restrict_mkst_fx. unfold kfl_ssM.
  apply pa_entry_st_ok_full.
  - unfold E, kfl_EM. apply regs_ok_Eimg_Ereg.
  - destruct withE; vm_compute; reflexivity.
  - destruct withE; cbn [app];
      repeat (apply Forall_cons; [first [exact RS | exact RC | exact RE] |]); apply Forall_nil.
  - destruct withE; cbn [app pairwise_disjoint all_disjoint]; unfold extent_disjoint, kfl_rS1, kfl_rCa, kfl_rE;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U18, ?U256;
      repeat split; lia.
  - split; [|split; [exact I | exact I]].
    unfold kfl_factsM. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U9, U18, U32, U33, U256.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    unfold SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the cut's registers as atoms of the built environment *)
Lemma kfl_at_ew : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md r v,
  kfl_at POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md ->
  In (r, v) (kfl_k0 cx ++ kfl_base_regs cx fpos ++ rl) -> Z.of_nat r = bv_unsigned (Z_to_bv 5 (Z.of_nat r)) ->
  ew (kfl_EM cx W3 ms0 ms) r = w64 v.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md r v HA Hin Hr.
  destruct HA as (_ & _ & (R2 & R9 & R8 & R3 & R4 & R18 & R20) & Hkre & _).
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - cbn [kfl_k0 In] in Hin.
    destruct Hin as [E | [E | [E | [E | [E | []]]]]]; injection E as <- <-.
    + rewrite (kfl_EM_reg cx W3 ms0 ms 2 2%bv eq_refl). exact R2.
    + rewrite (kfl_EM_reg cx W3 ms0 ms 9 9%bv eq_refl). exact R9.
    + rewrite (kfl_EM_reg cx W3 ms0 ms 8 8%bv eq_refl). exact R8.
    + rewrite (kfl_EM_reg cx W3 ms0 ms 18 18%bv eq_refl). exact R18.
    + rewrite (kfl_EM_reg cx W3 ms0 ms 20 20%bv eq_refl). exact R20.
  - rewrite (kfl_EM_reg cx W3 ms0 ms r _ Hr).
    unfold kregs_eq in Hkre. rewrite Forall_forall in Hkre. exact (Hkre (r, v) Hin).
Qed.

Lemma kfl_at_gp : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md,
  kfl_at POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md ->
  ew (kfl_EM cx W3 ms0 ms) 3 = getr (k_regs cx) 3 /\
  ew (kfl_EM cx W3 ms0 ms) 4 = getr (k_regs cx) 4.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 pc adv rl ms md HA.
  destruct HA as (_ & _ & (R2 & R9 & R8 & R3 & R4 & R18 & R20) & _).
  rewrite (kfl_EM_reg cx W3 ms0 ms 3 3%bv eq_refl), (kfl_EM_reg cx W3 ms0 ms 4 4%bv eq_refl).
  split; [exact R3 | exact R4].
Qed.

(* ==========================================================================
   THE INPUT BYTES: the shadow byte of p + i and the byte d[i], added to a state of the phase
   ========================================================================== *)
Lemma kfl_sbyte : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md i,
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md -> 0 <= i < k_wn cx ->
  mbyte SEGS (rdW W3 (ms_mem ms)) (kfl_q cx i) = Some (Z_to_bv 8 (kfl_s cx W3 ms0 i)) /\
  saddr_ok (k_wp cx + i) (kfl_s cx W3 ms0 i).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md i HM Hi.
  pose proof (proj1 HM) as HC.
  pose proof (kfl_ra0 _ _ _ _ _ _ _ _ _ HC) as (_ & _ & HRA).
  destruct (HRA (k_wp cx + i) ltac:(lia)) as (s & Hs & Hok).
  pose proof HC as (HB & _).
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (_ & _ & _ & _ & _ & HWP & HWN & HWPr & HWNr & _).
  assert (Hrd : kernel_ard SEGS (k_regs cx) (km0 cx) (k_wp cx + i)).
  { unfold kernel_ard. right; left. exists (k_wp cx), (k_wn cx). unfold ka0 in HWP, HWN.
    refine (conj HWP (conj HWN (conj HWPr (conj HWNr _)))). lia. }
  pose proof (kfl_input_pre cx HB) as (_ & _ & (_ & _ & _ & HAPc)).
  unfold apart in HAPc. fold (ka0 cx) in HAPc.
  destruct (kfl_UN_ard _ _ _ _ _ _ _ _ _ _ _ _ HM Hrd ltac:(lia)) as (_ & Esh).
  assert (Es : kfl_s cx W3 ms0 i = s) by (unfold kfl_s, kfl_q; unfold shadow_of_addr in Hs; rewrite Hs; reflexivity).
  rewrite Es. split; [|exact Hok].
  rewrite Hs in Esh. unfold kfl_q. unfold shadow_of_addr in Esh.
  unfold aview in Esh. destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms)) (SHADOW_OFF + (k_wp cx + i) / 8))
    as [b|] eqn:Eb; [|discriminate]. cbn in Esh. injection Esh as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma kfl_dbyte : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md i,
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md -> 0 <= i < k_wn cx ->
  mbyte SEGS (rdW W3 (ms_mem ms)) (k_wp cx + i) = Some (Z_to_bv 8 (kfl_d cx i)) /\ 0 <= kfl_d cx i < 256.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md i HM Hi.
  pose proof (proj1 HM) as HC.
  pose proof HC as (HB & _).
  pose proof HB as HB'. unfold kbase in HB'.
  destruct HB' as (_ & _ & _ & _ & _ & HWP & HWN & HWPr & HWNr & HD & HDl & _).
  assert (Hrd : kernel_ard SEGS (k_regs cx) (km0 cx) (k_wp cx + i)).
  { unfold kernel_ard. right; left. exists (k_wp cx), (k_wn cx). unfold ka0 in HWP, HWN.
    refine (conj HWP (conj HWN (conj HWPr (conj HWNr _)))). lia. }
  pose proof (kfl_input_pre cx HB) as (_ & _ & HAP).
  pose proof HAP as (_ & _ & _ & HAPc). unfold apart in HAPc. fold (ka0 cx) in HAPc.
  destruct (kfl_UN_ard _ _ _ _ _ _ _ _ _ _ _ _ HM Hrd ltac:(lia)) as (E1 & _).
  pose proof (kfl_apart_notE cx (k_wp cx) (k_wn cx) (k_wp cx + i) HAP ltac:(lia)) as HnE.
  pose proof (kfl_rd0 _ _ _ _ _ _ _ _ _ HC (k_wp cx + i) Hrd HnE) as E0.
  destruct HD as (_ & _ & HDb).
  pose proof (HDb (Z.to_nat i) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  rewrite (@nth_error_nth' _ (k_d cx) (Z.to_nat i) (Z_to_bv 8 0) ltac:(lia)) in Hb.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) (k_d cx) (Z_to_bv 8 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr.
  split; [|unfold kfl_d; exact Hr].
  rewrite (mbyte_of_aview SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) (ms_mem ms) (k_wp cx + i))
    by (rewrite E1; exact E0).
  unfold km0 in Hb. rewrite Hb. unfold kfl_d. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma kfl_rD_wf : forall i, (i < 3)%nat -> region_wf (kfl_rD i) = true.
Proof. intros i Hi. destruct i as [|[|[|i]]]; [vm_compute; reflexivity.. | lia]. Qed.
Lemma kfl_rQ_wf : forall i, region_wf (kfl_rQ i) = true.
Proof. intros i. reflexivity. Qed.

Lemma kfl_addq : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md E pc regs F k (i : nat),
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md ->
  st_ok_pi SEGS pa_val E (mkSS pc regs [kfl_rS1; kfl_rCa k] None F) (restrict (w_H W3) ms) ->
  (i < 3)%nat -> Z.of_nat i < k_wn cx ->
  ew E 9 = w64 (ksp1 cx) -> ew E 18 = w64 (ka0 cx) -> ew E 32 = w64 (k_wp cx) ->
  ew E (34 + i) = w64 (kfl_q cx (Z.of_nat i)) -> ew E (37 + i) = w64 (kfl_s cx W3 ms0 (Z.of_nat i)) ->
  ew E (40 + i) = w64 (kfl_d cx (Z.of_nat i)) ->
  st_ok_pi SEGS pa_val E
    (add_atom (add_atom (mkSS pc regs [kfl_rQ i; kfl_rD i; kfl_rS1; kfl_rCa k] None F) (37 + i) (mkAF 0 7 0))
       (40 + i) (mkAF 0 255 0))
    (restrict (w_H W3) ms).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md E pc regs F k i HM HS Hi3 Hi E9 E18 E32 Eq Es Ed.
  pose proof (proj1 HM) as HC.
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & Hs1m & Hwlo & Hwhi & HF4 & HFc & HF64 &
    HFSH & Ha0 & Ha0r & Hapf & Hwp0 & Hwpn & Hwn0 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  rewrite C3, C5 in Ha0r.
  pose proof HC as (HB & _).
  pose proof (kfl_input_pre cx HB) as (_ & _ & (HAPf & _ & _ & HAPc)).
  unfold apart, apart_frame in HAPc, HAPf. fold (ka0 cx) in HAPc. fold (ksp cx) in HAPf.
  destruct (kfl_sbyte _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat i) HM ltac:(lia)) as (Hsb & Hsok).
  destruct (kfl_dbyte _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat i) HM ltac:(lia)) as (Hdb & Hdr).
  assert (Hsr : 0 <= kfl_s cx W3 ms0 (Z.of_nat i) <= 7) by (unfold saddr_ok in Hsok; lia).
  assert (Uq : bv_unsigned (ew E (34 + i)) = kfl_q cx (Z.of_nat i))
    by (rewrite Eq; apply kfl_U; [reflexivity | unfold kfl_q, SHADOW_OFF; lia]).
  assert (U9 : bv_unsigned (ew E 9) = ksp1 cx) by (rewrite E9; apply kfl_U; [reflexivity | lia]).
  assert (U18 : bv_unsigned (ew E 18) = ka0 cx) by (rewrite E18; apply kfl_U; [reflexivity | lia]).
  assert (U32 : bv_unsigned (ew E 32) = k_wp cx) by (rewrite E32; apply kfl_U; [reflexivity | lia]).
  apply st_ok_pi_add_fact; [apply st_ok_pi_add_fact|].
  - apply (st_ok_pi_add_region E (mkSS pc regs [kfl_rD i; kfl_rS1; kfl_rCa k] None F) _ (kfl_rQ i)).
    + apply (st_ok_pi_add_region E (mkSS pc regs [kfl_rS1; kfl_rCa k] None F) _ (kfl_rD i)).
      * exact HS.
      * exact (kfl_rD_wf i Hi3).
      * unfold kfl_rD, region_ok. cbn [ms_mem restrict].
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (k_wp cx) (Z.of_nat i) 1 (SOff (40 + i) 0) (kfl_d cx (Z.of_nat i))).
        -- apply sv_off0. exact Ed.
        -- cbn. lia.
        -- cbn. lia.
        -- apply val_mem1_of_mbyte; [exact Hdr | exact Hdb].
      * cbn [ss_mem all_disjoint]. unfold extent_disjoint, kfl_rD, kfl_rS1, kfl_rCa.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U9, U18.
        repeat split; lia.
    + exact (kfl_rQ_wf i).
    + unfold kfl_rQ, region_ok. cbn [ms_mem restrict].
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uq.
      split; [unfold kfl_q, SHADOW_OFF; lia|]. split; [unfold kfl_q, SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (kfl_q cx (Z.of_nat i)) 0 1 (SOff (37 + i) 0) (kfl_s cx W3 ms0 (Z.of_nat i))).
      * apply sv_off0. exact Es.
      * cbn. lia.
      * cbn. lia.
      * rewrite Z.add_0_r. apply val_mem1_of_mbyte; [lia | exact Hsb].
    + assert (Happ : kfl_app (k_wp cx + Z.of_nat i)).
      { pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & HRD & _ & _ & _ & HWP & HWN & HWPr & HWNr & _).
        eapply kfl_akb_app; [exact (proj1 HPRE) | apply HRD].
        unfold kernel_ard. right; left. exists (k_wp cx), (k_wn cx). unfold ka0 in HWP, HWN.
        refine (conj HWP (conj HWN (conj HWPr (conj HWNr _)))). lia. }
      unfold kfl_app in Happ. rewrite C3, C5 in Happ.
      cbn [ss_mem all_disjoint]. unfold extent_disjoint, kfl_rQ, kfl_rD, kfl_rS1, kfl_rCa.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Uq, U32, U9, U18. unfold kfl_q, SHADOW_OFF.
      repeat split; (lia || (match goal with |- ?g => idtac "KFLG" g end; fail 1)).
  - unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (kfl_U _ _ Es ltac:(lia)). rewrite Z.pow_0_r, Z.mod_1_r. lia.
  - unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (kfl_U _ _ Ed ltac:(lia)). rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* the shadow entries of the cursor and of nl_errno.e at any state of the phase *)
Lemma kfl_shok : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md E,
  kfl_mid POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md ->
  ew E 18 = w64 (ka0 cx) -> ew E 20 = w64 SHADOW_OFF -> ew E (A_OBJ 15) = w64 LA_NL_ERRNO_E ->
  sh_ok SEGS kfl_Bx kfl_SH E (rdW W3 (ms_mem ms)).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md E HM E18 E20 E256.
  pose proof (proj1 HM) as HC.
  pose proof (kfl_nums _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & Hs1m & Hwlo & Hwhi & HF4 & HFc & HF64 &
    HFSH & Ha0 & Ha0r & Hapf & Hwp0 & Hwpn & Hwn0 & _ & HFa0).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  rewrite C3, C5 in Ha0r.
  pose proof (kfl_ra0 _ _ _ _ _ _ _ _ _ HC) as (HRc & HRe & _).
  pose proof HM as (_ & _ & _ & _ & (UN & _) & _).
  pose proof HC as (HB0 & _). pose proof HB0 as HB0'. unfold kbase in HB0'. destruct HB0' as (_ & _ & HKP & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAPe & _).
  destruct HAPe as (_ & _ & _ & HAPc). unfold apart in HAPc. fold (ka0 cx) in HAPc.
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  assert (UB : U E kfl_Bx = SHADOW_OFF) by (unfold kfl_Bx; apply U_atom; [exact E20 | unfold SHADOW_OFF; lia]).
  assert (U18 : U E (SOff 18 0) = ka0 cx) by (apply U_atom; [exact E18 | lia]).
  assert (U256 : U E (SOff (A_OBJ 15) 0) = LA_NL_ERRNO_E) by (apply U_atom; [exact E256 | unfold LA_NL_ERRNO_E; lia]).
  unfold sh_ok, kfl_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold shent_ok;
    cbn [she_m she_lo she_hi]; rewrite UB.
  - rewrite U18. split.
    + apply (ra_frame (aview SEGS (w_H W3) (ms_mem ms0))); [rewrite Z.add_0_r; exact HRc|].
      intros x Hx. rewrite Z.add_0_r in Hx.
      assert (Hrd : kernel_ard SEGS (k_regs cx) (km0 cx) x) by (unfold kernel_ard; left; unfold ka0 in Hx; lia).
      pose proof HC as (HB & _ & _ & HI & _).
      unfold kin_poison, kat in HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & Hkjb & _).
      pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md0 x HB Hkjb Hrd) as HnF.
      assert (Hfs16 : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfs16 in HnF.
      pose proof (kfl_shadow_out (kF cx fpos) x 2048 ltac:(lia)
        ltac:(lia) ltac:(lia) ltac:(lia)) as Hso.
      transitivity (aview SEGS (w_H W3) (ms_mem ms) (shadow_of_addr SHADOW_OFF x)); [reflexivity|].
      apply UN; [unfold shadow_of_addr, SHADOW_OFF; lia|].
      apply kfl_notX; unfold shadow_of_addr, SHADOW_OFF in *; [lia | lia |]. rewrite HFSH in *. lia.
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite ?U18 in Ha. rewrite ?UB.
      unfold SHADOW_OFF in *. lia.
  - rewrite U256. split.
    + apply (ra_frame (aview SEGS (w_H W3) (ms_mem ms0))); [rewrite Z.add_0_r; exact HRe|].
      intros x Hx. rewrite Z.add_0_r in Hx.
      assert (Hrd : kernel_ard SEGS (k_regs cx) (km0 cx) x)
        by (unfold kernel_ard; right; right; right; left; exact Hx).
      assert (Hnc : ~ (ka0 cx <= x < ka0 cx + 16)) by (unfold LA_NL_ERRNO_E in *; lia).
      destruct (kfl_UN_ard _ _ _ _ _ _ _ _ _ _ _ x HM Hrd Hnc) as (_ & Esh).
      transitivity (aview SEGS (w_H W3) (ms_mem ms) (shadow_of_addr SHADOW_OFF x)); [reflexivity | exact Esh].
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite ?U256 in Ha. rewrite ?UB.
      unfold LA_NL_ERRNO_E, SHADOW_OFF in *. lia.
Qed.

End b.
End a.

(* ---- the values of the engine's expressions at the atoms of a context ---- *)
Section h. Context {rc : YM05.RunCeil} {PI : PAImg link_listing}.

Definition kfl_a4 (cx : kcx) : Z := SHADOW_OFF + ka0 cx / 8.

Lemma kfl_d_off : forall E n v k v', ew E n = w64 v -> 0 <= v < 2 ^ 64 -> v + k = v' ->
  sv_denot E (SOff n k) = w64 v'.
Proof. intros E n v k v' Hn Hv <-. exact (kfl_den_off E n v k Hn Hv). Qed.

Lemma kfl_d_s8 : forall E cx, ew E 18 = w64 (ka0 cx) -> ew E 20 = w64 SHADOW_OFF -> 0 <= ka0 cx < 2 ^ 47 ->
  sv_denot E (kfl_e_sh 18 8) = w64 (kS8 cx).
Proof.
  intros E cx H18 H20 Hb.
  rewrite (kfl_den_sh E 18 8 (ka0 cx) SHADOW_OFF H18 ltac:(lia) ltac:(lia) H20 ltac:(unfold SHADOW_OFF; lia)
    ltac:(unfold SHADOW_OFF; lia)).
  reflexivity.
Qed.

Lemma kfl_d_a4 : forall E cx, ew E 18 = w64 (ka0 cx) -> ew E 20 = w64 SHADOW_OFF -> 0 <= ka0 cx < 2 ^ 47 ->
  sv_denot E (kfl_e_sh 18 0) = w64 (kfl_a4 cx).
Proof.
  intros E cx H18 H20 Hb.
  rewrite (kfl_den_sh E 18 0 (ka0 cx) SHADOW_OFF H18 ltac:(lia) ltac:(lia) H20 ltac:(unfold SHADOW_OFF; lia)
    ltac:(unfold SHADOW_OFF; lia)).
  unfold kfl_a4, w64. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma kfl_d_q : forall E cx i, ew E 32 = w64 (k_wp cx) -> ew E 20 = w64 SHADOW_OFF ->
  0 <= k_wp cx -> 0 <= i -> k_wp cx + i < 2 ^ 47 ->
  sv_denot E (kfl_e_sh 32 i) = w64 (kfl_q cx i).
Proof.
  intros E cx i H32 H20 H0 Hi Hb.
  rewrite (kfl_den_sh E 32 i (k_wp cx) SHADOW_OFF H32 ltac:(lia) ltac:(lia) H20 ltac:(unfold SHADOW_OFF; lia)
    ltac:(unfold SHADOW_OFF; lia)).
  reflexivity.
Qed.

Lemma kfl_d_a1 : forall E cx, ew E 18 = w64 (ka0 cx) -> 0 <= ka0 cx < 2 ^ 64 ->
  sv_denot E kfl_e_a1 = w64 (ka0 cx / 8).
Proof. intros E cx H18 Hb. exact (kfl_den_srl3 E 18 (ka0 cx) H18 Hb). Qed.

Lemma kfl_d_m6 : forall E n x y, ew E n = w64 x -> 0 <= x < 256 -> x mod 6 = y -> sv_denot E (kfl_m6 n) = w64 y.
Proof. intros E n x y Hn Hx <-. exact (kfl_den_m6 E n x Hn Hx). Qed.

Lemma kfl_br_eq0 : forall E n v k, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n k)) (sv_denot E (SLit 0)) = (v + k =? 0).
Proof.
  intros E n v k Hn Hv Hvk. rewrite branch_eq_U, (U_atom_off E n v k Hn Hv Hvk), U_lit by lia. reflexivity.
Qed.

Lemma kfl_br_ge : forall E n m v c s, ew E n = w64 v -> ew E m = w64 s ->
  0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 63 -> 0 <= s < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff n c) (SLit 7))) (sv_denot E (SOff m 0)) =
  negb ((v + c) mod 8 <? s).
Proof.
  intros E n m v c s Hn Hm Hv Hvc Hs.
  rewrite (kfl_den_and7 E n v c Hn Hv ltac:(lia)), (sv_off0 E m s Hm).
  apply kfl_bge; [pose proof (Z.mod_pos_bound (v + c) 8 ltac:(lia)); lia | exact Hs].
Qed.

End h.

Lemma kfl_d_reg : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* ==========================================================================
   THE WALK'S TACTICS (the segment files run them inside their Section, where SK B LAWS LV TL TB, the
   cut's facts U9 / U18 / U22 and the environment's facts `ew E n = ..` are bound)
   ========================================================================== *)
(* membership of a register pair in a cut's list *)
Ltac kfl_inl := cbn [kfl_k0 kfl_base_regs app In]; repeat (first [left; reflexivity | right]).

(* a register's value, from the symbolic value the engine left in it *)
Ltac kfl_den1 :=
  lazymatch goal with |- sv_denot ?E (sr_get ?rs ?r) = _ =>
    let e := eval vm_compute in (sr_get rs r) in
    replace (sr_get rs r) with e by (vm_compute; reflexivity);
    lazymatch e with
    | SLit _ => reflexivity
    | SOff _ 0 => apply kfl_d_reg; kfl_ew; eassumption
    | SOff _ _ => eapply kfl_d_off; [kfl_ew; eassumption | lia | lia]
    | SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) _) _ =>
        apply kfl_d_s8; [kfl_ew; eassumption | kfl_ew; eassumption | lia]
    | SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) _) _ =>
        apply kfl_d_a4; [kfl_ew; eassumption | kfl_ew; eassumption | lia]
    | SAlu ALU_SRL (SOff 18 0) _ => apply kfl_d_a1; [kfl_ew; eassumption | lia]
    | SAlu ALU_AND _ (SLit 255) => eapply kfl_d_m6; [kfl_ew; eassumption | lia | reflexivity]
    end
  end.

(* the writable windows of a run lie in the cursor and the slot *)
Ltac kfl_win :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Ha; cbn [ew ewset Nat.eqb] in Ha; repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Ha end;
     unfold kfl_Y; lia | ]);
  try destruct Hin.

(* the journal admits a run's writable windows *)
Ltac kfl_wr AWR HC :=
  eapply AWR; [exact HC|];
  let a := fresh "a" in let Ha := fresh "Ha" in let b := fresh "b" in let wlo := fresh "wlo" in
  let whi := fresh "whi" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in let Hq := fresh "Hq" in
  intros a Ha; destruct (in_wrange_windows _ _ _ Ha) as (b & wlo & whi & Hin & Hb); vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hb; cbn [ew ewset Nat.eqb] in Hb; repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hb end;
     unfold kfl_X; lia | ]);
  try destruct Hin.

(* a run's end state as the next state of the phase *)
Ltac kfl_step MSTEP HM msa msb HMn :=
  lazymatch goal with
  | HJx : ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msb) _ _,
    HFx : frame_of _ _ (mrestrict _ (ms_mem msa)) (mrestrict _ (ms_mem msb)),
    HGx : mem_grows (mrestrict _ (ms_mem msa)) (mrestrict _ (ms_mem msb)) |- _ =>
    pose proof (MSTEP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM HJx
      ltac:(repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
      ltac:(repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
      HFx ltac:(kfl_win) HGx) as HMn
  end.

(* the cut of the phase the run reached *)
Ltac kfl_exit_tac EXIT HMn HS :=
  eapply EXIT;
  [ exact HMn | exact HS | reflexivity | reflexivity
  | unfold kfl_regsP, kfl_k0, kfl_base_regs; cbn [app];
    repeat (apply Forall_cons; [cbv beta; cbn [fst snd]; kfl_den1 |]); apply Forall_nil
  | kfl_den1 | kfl_den1
  | vm_compute; repeat (first [left; reflexivity | right])
  | vm_compute; repeat (first [left; reflexivity | right])
  | cbn [ew ewset Nat.eqb]; eassumption | cbn [ew ewset Nat.eqb]; eassumption
  | cbn [ew ewset Nat.eqb]; eassumption | cbn [ew ewset Nat.eqb]; eassumption | lia ].

(* set register r of the state of HS to e' (the goal it leaves: the register's value is e''s) *)
Ltac kfl_setreg HS r e' :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?E ?ss (restrict ?H ?m) =>
    let Hg := fresh "Hg" in
    assert (Hg : getr (ms_regs (restrict H m)) (Z_to_bv 5 (Z.of_nat r)) = sv_denot E e');
    [ cbn [ms_regs restrict]; rewrite (st_ok_pi_restrict_reg H E ss m _ HS);
      lazymatch goal with |- sv_denot _ (sr_get ?rs ?rr) = _ =>
        let e := eval vm_compute in (sr_get rs rr) in
        replace (sr_get rs rr) with e by (vm_compute; reflexivity) end
    | let HS' := fresh "HS" in
      pose proof (st_ok_pi_set_reg E ss (restrict H m) (Z_to_bv 5 (Z.of_nat r)) e' HS
        ltac:(let Hq := fresh in intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) Hg)
        as HS';
      clear HS Hg; rename HS' into HS ]
  end.
