(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* put_string (A_put_string 0x85fc8, 928 bytes, preset_file.c:478-512), fs.asan-ubsan (image B): the walk's stretch and
   helper layer for lib/B/FSH_Fn_writer.v's put_string_spec (the CTX-drop text, by path from a working branch
   dda8331bd25). The closing theorem is lib/B/ZZpsfinal.v ps_put_string_spec over the four segments of ZZpsclose.ps_close.

   WHAT IS HERE. The walk's pure facts; the NAMED escape lemmas (under the spec's `plain_bytes bs` premise both escape
   arms are untaken, so the two-char arm, the four-hex arm and the snprintf call at PS_FMT_CALL 0x86214 are never
   reached); the loop's measured runs; the entry state; the stretch from the entry to the __asan_stack_malloc_0 call
   at PS_SM_CALL 0x86038; the registers at that call; the stretch from the call's return to the FIRST put call (the
   opening quote); one put call composed (ps_put_call); and the epilogue.

   CONTROL FLOW (MEASURED by vm_compute on the pinned fs.asan-ubsan through fsw_ps_tbl, never from a disassembly
   listing; each address below is the `ss_pc` of a symbolic run of that table; scratch probe lib/B/ZZpsM1.v of
   a Theorem Labs lane, 2026-10-29, not committed):
   - A_put_string 0x85fc8 .. PS_SM_CALL: frame 192, ra and s0..s11 saved at s0 - 8 .. s0 - 104, s0 := the entry sp,
     sp re-aligned down to 32 (`andi sp, sp, -32`), s1 := the re-aligned sp, the word at s0 - 192 cleared,
     s2 := the entry a1 (the string s; image A keeps it in s10), a2 := the use-after-return flag (1, from the two UAR
     cells; `beqz a2` not taken), s7 := the shadow base, a0 := 64 (class 0), ra := PS_SM_RET.  MEASURED:
     `sym_run_toN tfibsegs fsw_ps_tbl FUEL PC_stack_malloc_0 ps_ss0` is `RS_running` at PC_stack_malloc_0 0x3d4f4.
   - PS_SM_RET 0x8603c: the frame is granted (fs_fake_granted, via ps_grant), so `bnez a0` skips the real-stack
     fallback and the run joins at PS_JOIN 0x8606c.  The fallback is dead code.
   - PS_JOIN .. PS_OPEN_CALL 0x860d8: the frame address is kept in the re-aligned sp's slot at offset 80; the frame
     header (magic 0x41b58ab3, descriptor 0x123d5, pc 0x85fc8) is written at the frame + 0 / 8 / 16; the frame's shadow
     granule is written through s6 = the frame's shadow address (RE-SEATED on a fresh atom, FSW_K.fsw_reseat_atom);
     then put (a0 = o, a1 = PS_Q1 0x21240, a2 = 1, ra = PS_OPEN_RET 0x860dc).
   - B-ONLY CHECKS (UBSan; no image-A twin), each decided by the run, never reached: 0x860dc `beqz s2 -> 0x86354` (the
     null check of s, decided from atom 18's fact s >= 4096: the join's token run passes it, ZZpsjoin psj_runT);
     the loop head 0x86148 `addi s10, s4, -1` and the plain arm's 0x86174 `bne s10, -1` (the pointer-overflow check of
     q + 1, decided from atom 24's fact q <= 2 ^ 47 - 8: psl_runA passes it); 0x86234 `beq s10, -1` on the escape arm
     (unreachable under plain_bytes). UBSan's trap `unimp` 0x86354 is guarded by these three branches only.
   - THE LOOP (image B registers): at PS_HEAD 0x86148 s9 = x25 = the byte c, s2 = x18 = the run start r (= s),
     s4 = x20 = q + 1, s8 = x24 = q, s5 = x21 = the frame + 32, s6 = x22 = the frame's shadow, s7 = x23 = the shadow
     base, s3 = x19 = o. Image A holds c in s2 = x18, r in s10 = x26 and 34 in s9 = x25.
   Rule 24 (a Theorem Labs lane's brief, proof-index v5 built 2026-10-29T07:26:27Z from main@c4c03c57ba1; cold scan of 593
   lib/B trees, CONTROL `git grep -w A_put_string` passing; checker a Theorem Labs lane CONFIRM 08:4xZ): put_string has RELEASED
   proofs for fs's PLAIN and UBSAN builds only (lib/Prog, lib/U/Prog: templates only) and the A walk on
   a working branch ca67007c8c2 (this file's template); no lib/B FSW_put_string*.v or ZZps*.v exists on
   any working-branch ref. The old-line B walk lib/B/Prog/put_string*.v was not used. *)

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YCeo.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame FSW_frame3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- put_string's decoded code: the 232 words [tfib_A_put_string, tfib_E_put_string) of fs.asan-ubsan, in the
   donor's form (lib/A/FSW_writer_tbl.v at a working branch ca67007c8c2: build_table over the image's own
   bytes, table_ok by build_table_ok0). Image A's walk read put_string's words from FSW_writer_tbl.fsw_wr_tbl; this
   walk keeps its own table (the B-core fold owner a Theorem Labs lane's rule for the fold at a working branch
   a9edd281227). ---- *)
Definition FSW_PS_N : nat := 232%nat.          (* (tfib_E_put_string - tfib_A_put_string) / 4 = 928 / 4 *)
Lemma fsw_ps_extent : tfib_A_put_string + 4 * Z.of_nat FSW_PS_N = tfib_E_put_string.
Proof. unfold FSW_PS_N. cbv. reflexivity. Qed.
Definition fsw_ps_tbl_build : ctable := build_table tfibsegs tfib_A_put_string FSW_PS_N TEmpty.
Definition fsw_ps_tbl : ctable := Eval vm_compute in fsw_ps_tbl_build.
Lemma fsw_ps_tbl_eq : fsw_ps_tbl = fsw_ps_tbl_build.
Proof. vm_cast_no_check (eq_refl fsw_ps_tbl). Qed.
Lemma fsw_ps_tbl_ok : table_ok tfibsegs fsw_ps_tbl.
Proof.
  rewrite fsw_ps_tbl_eq. unfold fsw_ps_tbl_build.
  apply build_table_ok0. cbv. discriminate.
Qed.

(* ---- the addresses of put_string's own code that the walk cuts at. MEASURED: each is the `ss_pc` reached by a
   symbolic run of fsw_ps_tbl from the entry state (never read off a disassembly listing). ---- *)
Definition PS_FRAME_OWN : Z := 192.       (* the prologue's own sp drop; FRAME_put_string adds 31 + 64 *)
Definition PS_SM_CALL : Z := 0x86038.     (* jal __asan_stack_malloc_0 (PC_stack_malloc_0) *)
Definition PS_SM_RET : Z := 0x8603c.      (* its return address *)
Definition PS_JOIN : Z := 0x8606c.        (* the two frame arms join here *)
Definition PS_OPEN_CALL : Z := 0x860d8.   (* jal put, the opening quote *)
Definition PS_OPEN_RET : Z := 0x860dc.
Definition PS_HEAD : Z := 0x86148.        (* the scan loop head *)
Definition PS_ESC : Z := 0x86190.         (* the escape dispatch: UNREACHABLE under plain_bytes *)
Definition PS_FMT_CALL : Z := 0x86214.    (* jal snprintf: UNREACHABLE under plain_bytes (THE CUT) *)
Definition PS_END : Z := 0x8627c.         (* the terminating zero was seen *)
Definition PS_Q1 : Z := 0x21240.          (* the one-byte read-only string holding the quote byte 34 *)

(* ================= the NAMED escape lemmas (mandatory) ================= *)
(* Owner a Theorem Labs lane 20:38Z; two Theorem Labs lanes depend on them. put_string's loop head tests fs's
   `special` (preset_file.c:478-512: c = 34, c = 92, or c < 0x20) and branches to PS_ESC 0x86190 only when it
   holds; PS_ESC is the only predecessor of the two escape arms, and the snprintf call PS_FMT_CALL 0x86214 lies on
   both of them (the two-char arm for 34 / 92 and the four-hex arm for c < 0x20; the newline / tab / carriage-return escapes are
   __asan_memcpy copies, not snprintf). So it is enough to show that `special` is false at every byte of the
   string, which is what `plain_bytes` says, through FSW_writer_model.plain_not_special. *)

(* (1) every byte of a plain string fails fs's escape test: the branch at the loop head is NOT taken *)
Lemma ps_plain_not_special : forall bs c, plain_bytes bs -> In c bs -> WriterSpec.special c = false.
Proof.
  intros bs c H Hin. unfold plain_bytes in H. rewrite Forall_forall in H.
  exact (plain_not_special c (H c Hin)).
Qed.

(* (2) the escape test is false exactly on the bytes the walk reads, stated on the byte itself (the form the walk's
   branch obligation takes: the loaded byte is a byte of bs, so its three disjuncts all fail) *)
Lemma ps_plain_byte_arms : forall c, plain_byte c -> c <> 34 /\ c <> 92 /\ ~ (0 <= c < 32).
Proof. intros c (H32 & H34 & H92). split; [exact H34 | split; [exact H92 | lia]]. Qed.

(* (3) hence NO byte of a plain string reaches the escape dispatch PS_ESC, and so none reaches the snprintf call
   PS_FMT_CALL: the two-char arm and the four-hex arm are dead. This is the statement the three dependent lanes cite. *)
Lemma ps_no_escape_arm : forall bs,
  plain_bytes bs ->
  (forall c, In c bs -> WriterSpec.special c = false) /\
  (forall c, In c bs -> c <> 34 /\ c <> 92 /\ 32 <= c).
Proof.
  intros bs H. split.
  - intros c Hin. exact (ps_plain_not_special bs c H Hin).
  - intros c Hin. unfold plain_bytes in H. rewrite Forall_forall in H.
    destruct (H c Hin) as (H32 & H34 & H92).
    split; [exact H34 | split; [exact H92 | exact H32]].
Qed.

(* (4) what the walk then has to write: the opening quote, the bytes, the closing quote. FSW_writer_model's
   spieces_plain, named here as the walk's three-put shape. *)
Lemma ps_three_puts : forall bs, plain_bytes bs -> WriterSpec.spieces bs = [[34]; bs; [34]].
Proof. exact spieces_plain. Qed.

(* ================= the fake frame is granted ================= *)
(* put_string's spec allows FRL_CRT_CALLEE = 2 live frames at entry, and class 0 has fs_frames 0 = 2 ^ 14 slots, so
   count_cid 0 (frames S) < fs_frames 0, which is what fsw_stack_malloc_atU asks. (The same arithmetic as
   FSH_Fn_entry.fs_fake_granted; proved here so the walk does not import the ENTRY statement file.) *)
Lemma ps_grant : forall l : list (Z * Z), Z.of_nat (length l) <= FRL_CRT_CALLEE -> count_cid 0 l < fs_frames 0.
Proof.
  intros l Hl.
  assert (Hle : forall l' : list (Z * Z), count_cid 0 l' <= Z.of_nat (length l')).
  { induction l' as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? 0); lia. }
  assert (H14 : fs_frames 0 = 16384) by (vm_compute; reflexivity).
  rewrite H14. pose proof (Hle l). unfold FRL_CRT_CALLEE in Hl. lia.
Qed.
(* put's frames premise at put_string's three call sites: put_string's own class-0 frame rides on top, so the
   callee sees FRL_CRT_CALLEE + 1 frames. This is why put_spec takes `+ 1` (a Theorem Labs lane 22:44Z, accepted 22:46Z). *)
Lemma ps_frames_callee : forall (f : Z * Z) (l : list (Z * Z)),
  Z.of_nat (length l) <= FRL_CRT_CALLEE -> Z.of_nat (length (f :: l)) <= FRL_CRT_CALLEE + 1.
Proof. intros f l Hl. cbn [length]. lia. Qed.

(* ---- fs_heads depends only on ablocks (the frame grant keeps them) ---- *)
Lemma ps_heads : forall B ly S ly' S' U,
  ablocks B ly' S' = ablocks B ly S -> fs_heads B ly S U -> fs_heads B ly' S' U.
Proof. intros B ly S ly' S' U E H r Hr. rewrite E. exact (H r Hr). Qed.

(* a value chunk carries to another env that denotes its value the same (cbyte of a CVal reads only sv_denot) *)
Lemma ps_chunk_transfer : forall {fx : YK11.FPState} E1 E2 m base o w v1 v2,
  sv_denot E1 v1 = sv_denot E2 v2 ->
  YP09.chunk_ok tfibsegs E1 m base (YP09.mkChunk o (CVal w v1)) ->
  YP09.chunk_ok tfibsegs E2 m base (YP09.mkChunk o (CVal w v2)).
Proof.
intros fx E1 E2 m base o w v1 v2 Heq H i Hi. destruct (H i Hi) as (b & Hb & Hm). exists b. split; [|exact Hm].
cbn [YP09.cbyte YP09.c_val] in *. rewrite <- Heq. exact Hb.
Qed.

(* ================= the scan loop (a Theorem Labs lane's part, taken into this file by a Theorem Labs lane) =================
   Measured with vm_compute over fsw_ps_tbl. The loop head is PS_HEAD, its exit PS_END; under plain_bytes neither
   PS_ESC nor PS_FMT_CALL is ever entered (ps_no_escape_arm). ---- *)
Definition PSL_HEAD  : Z := PS_HEAD.
Definition PSL_END   : Z := PS_END.
Definition PSL_SHCHK : Z := 0x86250.   (* the inline shadow check of the byte at q + 1 *)
Definition PSL_LOAD  : Z := 0x86258.   (* the data load of that byte: THE CUT *)

(* ---- the loop head's symbolic state. Register convention at PS_HEAD 0x86148 (image B, MEASURED):
   s9 = x25 = the current byte c, s3 = x19 = o, s4 = x20 = q + 1, s5 = x21 = the frame + 32 (esc),
   s6 = x22 = the frame's SHADOW address, s7 = x23 = the shadow base (atom 32), s8 = x24 = q,
   s2 = x18 = the run start r, s10 = x26 = scratch (the head sets it to q for the pointer-overflow test),
   s1 = x9 = the re-aligned sp. Image A: c in x18, 34 in x25, r in x26. ---- *)
Definition psl_regs : list sv :=
  sr_set (sr_set sr_atoms 23%bv (SOff 32 0)) 20%bv (SOff 24 1).
Definition PSL_POIS : sv := SLit (2 ^ 64 - 8).   (* 0xf8, the scope-close byte the body stores back *)
(* the frame's eight shadow bytes f1 f1 f1 f1 f8 f3 f3 f3 (ps_fsh_chunks' values), in the order the body leaves
   them: its store at +4 moves that chunk to the front, so this order is a fixpoint of one loop iteration (MEASURED
   by a Theorem Labs lane, all three plain ranges). Carrying all eight - not only +4 - is what lets the walk rebuild the frame's
   shadow region after the loop (a Theorem Labs lane's finding: psl_iter keeps the memory only outside [shF, shF + 8)). *)
Definition psl_sh_region : YP09.region :=
  YP09.mkRegion (Some 22%nat) 0 8 0 8
    [YP09.mkChunk 4 (CVal 1 PSL_POIS);
     YP09.mkChunk 0 (CVal 1 (SLit 241)); YP09.mkChunk 1 (CVal 1 (SLit 241));
     YP09.mkChunk 2 (CVal 1 (SLit 241)); YP09.mkChunk 3 (CVal 1 (SLit 241));
     YP09.mkChunk 5 (CVal 1 (SLit 243)); YP09.mkChunk 6 (CVal 1 (SLit 243));
     YP09.mkChunk 7 (CVal 1 (SLit 243))].
Definition psl_byte_region : YP09.region := YP09.mkRegion (Some 24%nat) 1 2 0 0 [].
Definition psl_byte_region_c : YP09.region :=
  YP09.mkRegion (Some 24%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
Definition psl_atoms (lo hi : Z) : list (nat * afact) :=
  [(25%nat, mkAF lo hi 0); (21%nat, mkAF 4096 (2 ^ 47 - 8) 0);
   (22%nat, mkAF 4096 (2 ^ 47 - 8) 0); (24%nat, mkAF 4096 (2 ^ 47 - 8) 0);
   (18%nat, mkAF 4096 (2 ^ 47 - 8) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition psl_head (lo hi : Z) : sstate :=
  mkSS PSL_HEAD psl_regs [psl_sh_region; psl_byte_region] None (mkFacts (psl_atoms lo hi) [] []).
Definition psl_SH : list shent := [mkSHE 24 1 2].
Definition psl_K : nat := 60%nat.

(* the three ranges the plain-byte test splits into *)
Definition psl_rng (lo hi : Z) : Prop :=
  (lo = 32 /\ hi = 33) \/ (lo = 35 /\ hi = 91) \/ (lo = 93 /\ hi = 255).

(* ================= 1. the byte split ================= *)
Lemma psl_byte_split : forall c,
  plain_byte c -> c < 256 -> 32 <= c < 34 \/ 35 <= c < 92 \/ 93 <= c < 256.
Proof. intros c (H32 & H34 & H92) Hc. lia. Qed.

(* the same split in the form the walk uses it: the range fact the engine decides the two tests from *)
Lemma psl_byte_rng : forall c, plain_byte c -> c < 256 -> exists lo hi, psl_rng lo hi /\ lo <= c <= hi.
Proof.
  intros c H Hc. destruct (psl_byte_split c H Hc) as [HA | [HA | HA]].
  - exists 32, 33. split; [left; split; reflexivity | lia].
  - exists 35, 91. split; [right; left; split; reflexivity | lia].
  - exists 93, 255. split; [right; right; split; reflexivity | lia].
Qed.

(* ================= the measured runs ================= *)
(* A: the head to the inline shadow check of the byte at q + 1; nothing but the frame's shadow granule
   is written (0 at the scope open, 0xf8 at the scope close), so the region comes back as it went in. *)
Definition psl_ssA (lo hi : Z) : sstate :=
  fst (sym_run_toN tfibsegs fsw_ps_tbl FUEL PSL_SHCHK (psl_head lo hi)).
Lemma psl_runA : forall lo hi, psl_rng lo hi ->
  sym_run_toN tfibsegs fsw_ps_tbl FUEL PSL_SHCHK (psl_head lo hi) = (psl_ssA lo hi, RS_running)
  /\ ss_mem (psl_ssA lo hi) = [psl_sh_region; psl_byte_region]
  /\ ss_facts (psl_ssA lo hi) = mkFacts (psl_atoms lo hi) [] []
  /\ ss_resv (psl_ssA lo hi) = None.
Proof.
  intros lo hi [(-> & ->) | [(-> & ->) | (-> & ->)]];
    (split; [vm_compute; reflexivity | split; [vm_compute; reflexivity
     | split; vm_compute; reflexivity]]).
Qed.

(* B: the token run over the inline check, with the frame's shadow region dropped. *)
Definition psl_ssB (lo hi : Z) : sstate :=
  mkSS (ss_pc (psl_ssA lo hi)) (ss_regs (psl_ssA lo hi)) [psl_byte_region] None (ss_facts (psl_ssA lo hi)).
Definition psl_stB (lo hi : Z) : shst :=
  fst (sym_runN_tok tfibsegs fsw_ps_tbl psl_K fs_Bx fs_Bspan psl_SH FUEL (psl_ssB lo hi)).
Lemma psl_runB : forall lo hi, psl_rng lo hi ->
  sh_static_ok psl_K fs_Bx fs_Bspan psl_SH (ss_facts (psl_ssB lo hi)) (ss_mem (psl_ssB lo hi)) = true
  /\ sym_runN_tok tfibsegs fsw_ps_tbl psl_K fs_Bx fs_Bspan psl_SH FUEL (psl_ssB lo hi)
       = (psl_stB lo hi, TS_stopped (SR_load (Some 24%nat) 1))
  /\ sh_obls (psl_stB lo hi) = []
  /\ sh_j (psl_stB lo hi) = 2%nat
  /\ ss_pc (sh_ss (psl_stB lo hi)) = PSL_LOAD
  /\ ss_mem (sh_ss (psl_stB lo hi)) = [psl_byte_region]
  /\ ss_facts (sh_ss (psl_stB lo hi)) = mkFacts (psl_atoms lo hi) [] []
  /\ ss_resv (sh_ss (psl_stB lo hi)) = None.
Proof.
  intros lo hi [(-> & ->) | [(-> & ->) | (-> & ->)]];
    (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
    (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
    (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
    (split; vm_compute; reflexivity).
Qed.

(* C: the cut at the data load, then on. blo/bhi is the NEXT byte's range. *)
Definition psl_ssC (lo hi blo bhi : Z) : sstate :=
  add_atom (mkSS PSL_LOAD (ss_regs (sh_ss (psl_stB lo hi))) [psl_byte_region_c] None
              (mkFacts (psl_atoms lo hi) [] [])) 33%nat (mkAF blo bhi 0).
Definition psl_ssD (lo hi blo bhi : Z) : sstate :=
  fst (sym_run_toN tfibsegs fsw_ps_tbl FUEL PSL_HEAD (psl_ssC lo hi blo bhi)).

(* D: the plain run from the cut back to the loop head (the next byte is not the terminating zero) *)
Lemma psl_runD : forall lo hi, psl_rng lo hi ->
  sym_run_toN tfibsegs fsw_ps_tbl FUEL PSL_HEAD (psl_ssC lo hi 1 255) = (psl_ssD lo hi 1 255, RS_running)
  /\ ss_pc (psl_ssD lo hi 1 255) = PSL_HEAD
  /\ ss_mem (psl_ssD lo hi 1 255) = [psl_byte_region_c]
  /\ ss_resv (psl_ssD lo hi 1 255) = None.
Proof.
  intros lo hi [(-> & ->) | [(-> & ->) | (-> & ->)]];
    (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
    (split; vm_compute; reflexivity).
Qed.

(* E: the loop's shift. The next head's pointer is q + 1, so atom 24 moves up by one; the facts of the
   two bytes (25 and 33) are dropped here and rebuilt after the shift. *)
Definition psl_rb : rebase := [(24%nat, (24%nat, -1))].
Definition psl_G : facts :=
  mkFacts [(21%nat, mkAF 4096 (2 ^ 47 - 8) 0); (22%nat, mkAF 4096 (2 ^ 47 - 8) 0);
           (24%nat, mkAF 4096 (2 ^ 47 - 8) 0); (18%nat, mkAF 4096 (2 ^ 47 - 8) 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition psl_ssF (lo hi : Z) : sstate := ss_rebase psl_rb (psl_ssD lo hi 1 255) psl_G.

(* ---- the walk's semantic reading of the head's atoms ---- *)
Definition psl_at (E : env) (c q esc shF o r : Z) : Prop :=
  bv_unsigned (ew E 25) = c /\ bv_unsigned (ew E 21) = esc /\ bv_unsigned (ew E 22) = shF /\
  bv_unsigned (ew E 24) = q /\ bv_unsigned (ew E 18) = r /\ bv_unsigned (ew E 19) = o /\
  ew E 32 = Z_to_bv 64 SHADOW_OFF.
Definition psl_bd (c q esc shF r lo hi : Z) : Prop :=
  lo <= c <= hi /\ 4096 <= esc <= 2 ^ 47 - 8 /\ 4096 <= shF <= 2 ^ 47 - 8 /\
  4096 <= q <= 2 ^ 47 - 8 /\ 4096 <= r <= 2 ^ 47 - 8.

Lemma psl_afact : forall E n v lo hi,
  bv_unsigned (ew E n) = v -> lo <= v <= hi -> afact_ok E n (mkAF lo hi 0).
Proof.
  intros E n v lo hi Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Hv, Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.
Lemma psl_facts_ok : forall E c q esc shF o r lo hi,
  psl_at E c q esc shF o r -> psl_bd c q esc shF r lo hi ->
  facts_ok E (mkFacts (psl_atoms lo hi) [] []).
Proof.
  intros E c q esc shF o r lo hi (E25 & E21 & E22 & E24 & E18 & E19 & E32) (Bc & Be & Bs & Bq & Br).
  assert (E32u : bv_unsigned (ew E 32) = SHADOW_OFF)
    by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
  split; [|split; exact I]. cbn [psl_atoms atoms_ok].
  split; [exact (psl_afact E 25 c lo hi E25 Bc)|].
  split; [exact (psl_afact E 21 esc _ _ E21 Be)|].
  split; [exact (psl_afact E 22 shF _ _ E22 Bs)|].
  split; [exact (psl_afact E 24 q _ _ E24 Bq)|].
  split; [exact (psl_afact E 18 r _ _ E18 Br)|].
  assert (H32 : afact_ok E 32 (mkAF SHADOW_OFF SHADOW_OFF 0))
    by exact (psl_afact E 32%nat SHADOW_OFF SHADOW_OFF SHADOW_OFF E32u (conj (Z.le_refl _) (Z.le_refl _))).
  split; [exact H32 | exact I].
Qed.
Lemma psl_G_ok : forall E c q esc shF o r lo hi,
  psl_at E c q esc shF o r -> psl_bd c q esc shF r lo hi -> facts_ok E psl_G.
Proof.
  intros E c q esc shF o r lo hi HAT HBD.
  pose proof (psl_facts_ok E c q esc shF o r lo hi HAT HBD) as (HA & _).
  cbn [psl_atoms atoms_ok] in HA. destruct HA as (_ & H21 & H22 & H24 & H18 & H32 & _).
  unfold psl_G. split; [cbn [f_atoms atoms_ok]; tauto | split; exact I].
Qed.

(* a run whose every region is read-only changes no byte at all *)
Lemma psl_frame_ro : forall E rs (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
  intros E rs m m' Hro HF x. apply HF. intros (r & Hin & Hr).
  rewrite Forall_forall in Hro. pose proof (Hro r Hin). lia.
Qed.

(* `wview` and `mbyte` read the memory only at the address asked, so a region keeps its region_ok
   under a memory that agrees everywhere (the core's writable_iff_of is inside the malloc section) *)
Lemma psl_region_ok_eq : forall E (m m' : word -> option byte) r,
  (forall x, m' x = m x) -> region_ok tfibsegs E m r -> region_ok tfibsegs E m' r.
Proof.
  intros E m m' r Hm (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
  - intros oo Ho. unfold writable_at, wview in *. rewrite Hm. exact (H3 oo Ho).
  - rewrite Forall_forall in H4 |- *. intros cc Hc i Hi.
    destruct (H4 cc Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
    unfold mbyte in *. rewrite Hm. exact Hb2.
Qed.

(* the state at the data-load cut names no atom 33, so the walk may seat the loaded byte there *)
Lemma psl_on33 : forall lo hi, psl_rng lo hi ->
  YCeo.ss_atoms_on (fun n => negb (Nat.eqb n 33)) (sh_ss (psl_stB lo hi)) = true.
Proof. intros lo hi [(-> & ->) | [(-> & ->) | (-> & ->)]]; vm_compute; reflexivity. Qed.

(* ---- the rest of a Theorem Labs lane's scan-loop helpers, ported here (its scratch is parked at
   a working branch 88c60453b45; that branch does not build as-is on this base) ---- *)

(* ---- the shift's closed data: the register file and the state the rebase lands on ---- *)
Definition psl_regsF : list sv := Eval vm_compute in (regs_rebase psl_rb (ss_regs (psl_ssD 35 91 1 255))).
Definition psl_byte_regionF : YP09.region := Eval vm_compute in (region_rebase psl_rb psl_byte_region_c).
Definition psl_ssF' : sstate := mkSS PSL_HEAD psl_regsF [psl_byte_regionF] None psl_G.
Definition psl_ssG : sstate := mkSS PSL_HEAD psl_regsF [] None psl_G.
Lemma psl_runF : forall lo hi, psl_rng lo hi ->
  ss_rebase psl_rb (mkSS (ss_pc (psl_ssD lo hi 1 255)) (ss_regs (psl_ssD lo hi 1 255))
                         (ss_mem (psl_ssD lo hi 1 255)) (ss_resv (psl_ssD lo hi 1 255)) psl_G) psl_G
  = psl_ssF'.
Proof. intros lo hi [(-> & ->) | [(-> & ->) | (-> & ->)]]; vm_compute; reflexivity. Qed.
(* after the shift the FIVE scratch registers hold atoms 24 / 60 / 61 / 33 and q - 1 (image B, MEASURED: x10 = q, x11 /
   x12 = the two shadow-check tokens, x25 = the next byte, x26 = s10 = the previous q, which image B's loop head sets
   for its pointer-overflow test); the state names none of 10, 11, 12, 25, 26, so the walk may seat them there and
   recover psl_regs exactly *)
Lemma psl_on_scratch :
  YCeo.ss_atoms_on
    (fun n => negb (orb (orb (orb (Nat.eqb n 10) (Nat.eqb n 11)) (orb (Nat.eqb n 12) (Nat.eqb n 25)))
                        (Nat.eqb n 26)))
    psl_ssG = true.
Proof. vm_compute; reflexivity. Qed.
Lemma psl_regsF_set :
  sr_set (sr_set (sr_set (sr_set (sr_set psl_regsF 10%bv (SOff 10 0)) 11%bv (SOff 11 0))
            12%bv (SOff 12 0)) 25%bv (SOff 25 0)) 26%bv (SOff 26 0) = psl_regs.
Proof. vm_compute; reflexivity. Qed.

(* ---- small-context arithmetic and env lemmas (never proved inside a walk's context: `lia` there
   preprocesses every run hypothesis and does not come back) ---- *)
Lemma psl_bd_shift : forall c q esc shF r lo hi d lo' hi',
  psl_bd c q esc shF r lo hi -> q + 1 <= 2 ^ 47 - 8 -> lo' <= d <= hi' ->
  psl_bd d (q + 1) esc shF r lo' hi'.
Proof. unfold psl_bd. intros c q esc shF r lo hi d lo' hi' H H1 H2. lia. Qed.
Lemma psl_bd_q64 : forall c q esc shF r lo hi, psl_bd c q esc shF r lo hi -> 0 <= q + 1 < 2 ^ 64.
Proof. unfold psl_bd. intros c q esc shF r lo hi H. lia. Qed.
Lemma psl_rebase_ok : forall E E' q,
  bv_unsigned (ew E 24) = q -> bv_unsigned (ew E' 24) = q + 1 ->
  (forall n, n <> 24%nat -> ew E' n = ew E n) -> ed E' = ed E ->
  rebase_ok E E' psl_rb.
Proof.
  intros E E' q H24 H24' Hoth Hed. split; [|split].
  - intros n n' dd Hl. unfold psl_rb in Hl. cbn [rb_lookup] in Hl.
    destruct (Nat.eqb 24 n) eqn:Hn; [|discriminate Hl].
    apply Nat.eqb_eq in Hn. subst n. injection Hl as <- <-.
    rewrite H24, H24'. f_equal. lia.
  - intros n Hl. apply Hoth. intros ->. unfold psl_rb in Hl. cbn in Hl. discriminate Hl.
  - exact Hed.
Qed.
Lemma psl_lit_denot : forall E z, sv_denot E (SLit z) = Z_to_bv 64 (zcanon z).
Proof. intros E z. rewrite denot_lit_U, U_SLit. reflexivity. Qed.
Lemma psl_chunk_lit_env : forall E E' m base (w : N) z off,
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal w (SLit z))) ->
  YP09.chunk_ok tfibsegs E' m base (YP09.mkChunk off (CVal w (SLit z))).
Proof.
  intros E E' m base w z off H i Hi. cbn [YP09.c_len YP09.c_off YP09.c_val] in Hi |- *.
  destruct (H i Hi) as (b & H1 & H2). exists b. split; [|exact H2].
  cbn [YP09.c_off YP09.c_val YP09.cbyte] in H1 |- *.
  rewrite (psl_lit_denot E' z). rewrite (psl_lit_denot E z) in H1. exact H1.
Qed.
Lemma psl_sh_env : forall E E' m,
  bv_unsigned (ew E' 22) = bv_unsigned (ew E 22) ->
  region_ok tfibsegs E m psl_sh_region -> region_ok tfibsegs E' m psl_sh_region.
Proof.
  intros E E' m H HR. unfold psl_sh_region, region_ok, PSL_POIS in HR |- *.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR |- *.
  rewrite H. destruct HR as (A & Bb & C & D). split; [exact A|]. split; [exact Bb|]. split; [exact C|].
  rewrite Forall_forall in D |- *. intros cc Hcc. specialize (D cc Hcc). cbn [In] in Hcc.
  repeat (destruct Hcc as [<-|Hcc]; [exact (psl_chunk_lit_env E E' m _ _ _ _ D)|]). destruct Hcc.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the image cells of B. The shadow-base pair is S0's ONE named hypothesis FsShadowSyms (FSH_Base.v:116, owner
   RELOC: discharged by lib/A/ACeg.v's TfibLib once lib/A/ACej.v builds); FSW_K's entry takes its two projections.
   The use-after-return pair has no S0 name yet (owner RELOC, the same TfibLib: tl_got_uar / tl_uar_cell). *)
(* put's S0 contract: the callee hypothesis, discharged at composition by the put lane's walk. No CTX binder: the
   writer specs dropped it (owner ruling 05:05Z). *)
Hypothesis HPUT : FSH_Fn_writer.put_spec B tfibsegs.
Hypothesis HSS : FsShadowSyms B.
(* the runtime's laws and fake-frame contract, as FSW_frame.fsw_stack_malloc_atU takes them (its Section arguments):
   api_env / model_laws / stack_malloc_progressP are the unit's runtime laws (owner RUNTIME, the donor's TfibLib
   gives them); astack_malloc_realizesU is FSupoisonU's statement of __asan_stack_malloc (owner a Theorem Labs lane, walk open);
   HSMPC is B's code map at class 0 (owner RELOC: TfibLib's tl_code, fs's class map 0 -> 0x3d484). *)
Hypothesis HENV : api_env tfibsegs B.
Hypothesis HML : model_laws (as_universe B).
Hypothesis HSMP : stack_malloc_progressP B.
Hypothesis HSM0 : astack_malloc_realizesU tfibsegs B 0.
Hypothesis HSMPC : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0.
(* the fake frame's release laws, as FSW_frame.fsw_flag_storeU takes them (owner RUNTIME, the donor's TfibLib) *)
Hypothesis HASF : astack_free_law tfibsegs B.
Hypothesis HFFL : frame_flag_lawP tfibsegs B.
Let HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 HSS.
Let HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 HSS.

(* ---- the kit steps this walk uses are all PROVED and imported by path, none is a hypothesis:
   FSW_frame.fsw_stack_malloc_atU and FSW_frame3.fsw_flag_storeU / fsw_after_callU_s0_ot (a Theorem Labs lane,
   a working branch 2fe0e09c2c7, taken by path; the after-call takes the four-arm FP relation, so
   ps_put_call states that form, not FSW_K3's five-arm fsw_fp_sub), FSW_ret.fsw_retU / fsw_fpreU_atFP
   (a Theorem Labs lane). ---- *)

(* the use-after-return cell pair; owner RELOC, the same TfibLib (tl_got_uar / tl_uar_cell). No S0 name yet. *)
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.

(* ================= the entry state and the stretch to the stack_malloc call ================= *)
(* fss0T_args: the two shadow-base cells, the two use-after-return cells, and the 192-byte frame of the prologue *)
Definition ps_ss0 : sstate := fss0T_args A_put_string PS_FRAME_OWN fs_uar_regions [].

Lemma ps_entry : forall ly S U (W : world tfibsegs) regs mem md ch,
  afn_preU tfibsegs B STK_put_string ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) ps_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_put_string) mem (seg_rom tfibsegs))).
Proof.
intros ly S U W regs mem md ch HPRE.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_put_string = ltac:(let v := eval vm_compute in STK_put_string in exact v)) by reflexivity.
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
apply (fsw_entryT_args B _ PS_FRAME_OWN ly S U W regs mem md ch _ fs_uar_regions [] HGOT HCELL HPRE).
- unfold PS_FRAME_OWN. lia.
- vm_compute. reflexivity.
- exact (fsw_uar_regions_ok B _ ly S U W regs mem md ch _ HGUAR HUCELL HPRE).
- apply pairwise_disjoint_of_extents.
  unfold fsT_regions_args, fsT_regions, fs_uar_regions, fs_got_uar_region, fs_uar_cell_region, fs_got_region,
    fs_bcell_region, fstk, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, fs_D_GOT_uar,
    fs_D_uar_cell.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, PS_FRAME_OWN. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- exact I.
Qed.

(* ---- the symbolic state at the RETURN of __asan_stack_malloc_0 (PS_SM_RET).
   Regions (MEASURED to be the only ones the stretch to put needs): the saved words at the s0 atom 8, window
   [-192, 0); the re-aligned stack frame at atom 9 (s1), window [0, 192) - the frame-pointer slot at offset 80
   lives there; and the granted fake frame at atom 10 (a0 of the resumed registers), window [0, 64), with its
   flag word at offset 56. The entry atoms of the thirteen saved registers are xatom 0 .. xatom 12 (33 .. 45),
   in the env's extra list after the shadow base (FSW_K's atom convention).
   The atom facts take af_hi = 2 ^ 47 - n, never 2 ^ 47 (a Theorem Labs lane 23:26Z, measured by a Theorem Labs lane on FSW_put.v:
   the token engine's static check asks that (af_hi + she_hi - 1) / 8 still lie in Bspan). ---- *)
Definition ps_sv_chunks : list YP09.chunk :=
  map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (xatom k) 0))) (seq 0 13).
Definition ps_resume_regions : list YP09.region :=
  [YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 ps_sv_chunks;
   YP09.mkRegion (Some 9%nat) 0 88 0 88 [];
   YP09.mkRegion (Some 10%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff (xatom 13) 0))]].
Definition ps_resume_ss (r : Z) : sstate :=
  mkSS r (sr_set sr_atoms 23%bv (SOff 32 0)) ps_resume_regions None
    (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 88) 5);
              (10%nat, mkAF 4096 (2 ^ 47 - 64) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
(* the env at the resume: the shadow base, then the thirteen saved entry words, then the frame's flag address *)
Definition ps_xs (regs : bvmap 5 word) (flag : Z) : list word :=
  [YK11.getr regs 1%bv; YK11.getr regs 8%bv; YK11.getr regs 9%bv; YK11.getr regs 18%bv; YK11.getr regs 19%bv;
   YK11.getr regs 20%bv; YK11.getr regs 21%bv; YK11.getr regs 22%bv; YK11.getr regs 23%bv; YK11.getr regs 24%bv;
   YK11.getr regs 25%bv; YK11.getr regs 26%bv; YK11.getr regs 27%bv; Z_to_bv 64 flag].

Lemma ps_resume_sm : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc S2 U (W : world tfibsegs) memT mdc mem2 md2 k
  pos sp1 regs0 regs2,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc S2 U W mem2 md2 -> ARU tfibsegs B lyc Sc U W memT mdc ->
  acall_kept tfibsegs B lyc Sc W (unpoison U memT) W (unpoison U mem2) (sp1 - ESTACK) sp1 (fun _ => False) ->
  In (0, pos) (frames S2) ->
  YK11.getr regs2 8%bv = Z_to_bv 64 sp0 -> YK11.getr regs2 9%bv = Z_to_bv 64 sp1 ->
  YK11.getr regs2 10%bv = Z_to_bv 64 (frame_addr lyc 0 pos) ->
  YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF ->
  rdword (aview tfibsegs (w_H W) mem2) (frame_addr lyc 0 pos + fs_frame_bytes 0 - 8)
    = Some (flag_addr lyc 0 pos) ->
  sp0 - 208 <= sp1 <= sp0 - 192 -> sp0 - STK <= sp1 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> sp1 mod 32 = 0 ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ ps_xs regs0 (flag_addr lyc 0 pos)))
            (mrestrict (w_H W) memT) sp0) ps_sv_chunks ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ ps_xs regs0 (flag_addr lyc 0 pos))) (ps_resume_ss PS_SM_RET)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 PS_SM_RET) mem2 (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc S2 U W memT mdc mem2 md2 k pos sp1 regs0 regs2
  HJ HARU2 HARUc Hkept Hin E8 E9 E10 E23 Hflag Hsp1 Hwin H47 Hal16 Hsp32 Hcs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47b & Hbot & Htop & Htop2).
pose proof (ARU_AR tfibsegs B lyc S2 U W mem2 md2 HARU2) as HAR2.
destruct (al_frames _ _ LAWS lyc S2 W (unpoison U mem2) md2 0 pos HAR2 Hin) as (Hal32 & _ & Hfp & _).
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (unpoison U mem2) md2 0 pos HAR2 Hin) as (H4096 & Hfc & _).
destruct (al_flag _ _ LAWS lyc S2 W (unpoison U mem2) md2 0 pos HAR2 Hin) as (_ & _ & Hflapp & _).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
assert (FL4096 : 4096 <= FL /\ FL + 1 <= 2 ^ 64)
  by (unfold in_app, kLowShadowBeg, ASAN_CEIL in Hflapp; lia).
set (X := fs_extraT ++ ps_xs regs0 FL) in *.
assert (U8 : bv_unsigned (ew (Ereg regs2 X) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs2 X 8 8%bv eq_refl), E8; apply wz; lia).
assert (U9 : bv_unsigned (ew (Ereg regs2 X) 9) = sp1)
  by (rewrite (ew_Ereg_nat regs2 X 9 9%bv eq_refl), E9; apply wz; lia).
assert (U10 : bv_unsigned (ew (Ereg regs2 X) 10) = F)
  by (rewrite (ew_Ereg_nat regs2 X 10 10%bv eq_refl), E10; apply wz; lia).
assert (U32 : ew (Ereg regs2 X) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U46 : ew (Ereg regs2 X) (xatom 13) = Z_to_bv 64 FL)
  by (unfold xatom; change (33 + 13)%nat with (32 + 14)%nat; rewrite ew_Ereg_extra; reflexivity).
(* the resumed state with the plain atom register file, then s7 re-read as the shadow-base atom *)
assert (HS0 : st_ok tfibsegs (Ereg regs2 X) (mkSS PS_SM_RET sr_atoms ps_resume_regions None (ss_facts (ps_resume_ss PS_SM_RET)))
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 PS_SM_RET) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ps_resume_regions. constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [lia|]. split.
      * intros q Hq. apply (apresent_writable tfibsegs).
        apply (fsw_apresent_unpoison B lyc S2 U W mem2 md2 _ HARU2); [lia|]. apply Hpres. lia.
      * apply Forall_forall. intros c Hc.
        pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
        assert (Hci : -104 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0).
        { unfold ps_sv_chunks in Hc. apply in_map_iff in Hc as (kk & <- & Hkk).
          apply in_seq in Hkk. cbn. lia. }
        apply (chunk_ok_mbyte _ (mrestrict (w_H W) memT)); [|exact Hck].
        intros i Hi. apply (mbyte_of_aview tfibsegs).
        rewrite <- (fsw_aview_unpoison_high B lyc S2 U W mem2 md2 _ HARU2) by lia.
        rewrite <- (fsw_aview_unpoison_high B lyc Sc U W memT mdc _ HARUc) by lia.
        destruct Hkept as (K1 & _). apply K1; lia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros q Hq. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B lyc S2 U W mem2 md2 _ HARU2); [lia|]. apply Hpres. lia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U10. split; [lia|]. split; [lia|]. split.
      * intros q Hq. apply (apresent_writable tfibsegs).
        destruct (Hfp (F + q) ltac:(rewrite Hfb in *; lia)) as (Hp & Hno).
        exact (fsw_apresent_notowned B lyc S2 U W mem2 md2 (F + q) HARU2 ltac:(lia) Hno Hp).
      * constructor; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs (Ereg regs2 X) _ F 56 8 (SOff (xatom 13) 0) FL);
          [rewrite fsw_SOff0, U46; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia|].
        cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        replace (F + 56) with (F + fs_frame_bytes 0 - 8) by (rewrite Hfb; lia).
        exact (val_mem_of_rdword tfibsegs (w_H W) mem2 _ _ Hflag).
  - apply pairwise_disjoint_of_extents. unfold ps_resume_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U9, U10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - split; [|split; exact I]. cbn [ss_facts ps_resume_ss f_atoms atoms_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U9, U10, U32, (wz SHADOW_OFF ltac:(unfold SHADOW_OFF; lia)).
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r.
    repeat match goal with |- _ /\ _ => split end;
      first [exact I | exact Hal16 | exact Hsp32 | exact Hal32 | apply Z.mod_1_r
            | rewrite Hfb in *; unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]. }
exact (st_ok_set_reg tfibsegs (Ereg regs2 X) _ _ 23%bv (SOff 32 0) HS0 ltac:(discriminate)
  ltac:(cbn [ms_regs restrict mkst]; rewrite fsw_SOff0, U32; exact E23)).
Qed.


(* the state at the __asan_stack_malloc_0 call site (MEASURED: `sym_run_toN tfibsegs fsw_ps_tbl FUEL
   PC_stack_malloc_0 ps_ss0` is RS_running there) *)
Definition ps_ss1 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs fsw_ps_tbl FUEL PC_stack_malloc_0 ps_ss0).

(* ---- segment 0: the prologue, the re-align, the use-after-return test, up to the call of
   __asan_stack_malloc_0 at PS_SM_CALL. Nothing here allocates, so the journal is the initial one. ---- *)
Lemma ps_seg0 : forall ly S U (W : world tfibsegs) regs mem md ch FP (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_put_string ly S U W regs mem md ch ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs fs_extraT) ps_ss1 (restrict (w_H W) ms) ->
     ajournal tfibsegs B STK_put_string (spZ regs) FP ly S W (unpoison U mem) md [] ly S W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
     frame_of (Ereg regs fs_extraT) (ss_mem ps_ss0) mem (ms_mem ms) ->
     frame_of (Ereg regs fs_extraT) (ss_mem ps_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put_string regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP Q HPRE K.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_put_string = ltac:(let v := eval vm_compute in STK_put_string in exact v)) by reflexivity.
pose proof (ps_entry ly S U W regs mem md ch HPRE) as HS.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
pose proof (ajournal_init tfibsegs B STK_put_string FP ly S W regs (unpoison U mem) md ch (proj1 HPRE)) as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_put_string) with (Z_to_bv 64 A_put_string).
fsw_aj_run_toU fsw_ps_tbl_ok HS HJ HARU PC_stack_malloc_0.
{ awr_ok_tac. exact Usp. }
exact (K _ _ HS HJ HARU HF HFr).
Qed.

(* the registers at the call of __asan_stack_malloc_0, read off ps_ss1 (MEASURED): sp = s1 = the re-aligned sp
   (the 192-byte drop, then down to 32), a0 = 64 (class 0), a2 = 1 (the use-after-return flag: the `beqz a2`
   before the call is NOT taken), ra = PS_SM_RET, gp / tp kept, s0 = the entry sp, s7 = the shadow base,
   s3 = the entry a0 (the out-object o), s2 = x18 = the entry a1 (the string s; image A kept it in s10). *)
Lemma ps_sm_site : forall ly S U (W : world tfibsegs) regs mem md ch ms,
  afn_preU tfibsegs B STK_put_string ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) ps_ss1 (restrict (w_H W) ms) ->
  YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (32 * ((spZ regs - PS_FRAME_OWN) / 32)) /\
  YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (32 * ((spZ regs - PS_FRAME_OWN) / 32)) /\
  spZ regs - PS_FRAME_OWN - 16 <= 32 * ((spZ regs - PS_FRAME_OWN) / 32) <= spZ regs - PS_FRAME_OWN /\
  (32 * ((spZ regs - PS_FRAME_OWN) / 32)) mod 32 = 0 /\
  YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 PS_SM_RET /\ YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 64 /\
  YK11.getr (ms_regs ms) 12%bv = Z_to_bv 64 1 /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs 3%bv /\ YK11.getr (ms_regs ms) 4%bv = YK11.getr regs 4%bv /\
  YK11.getr (ms_regs ms) 8%bv = YK11.getr regs 2%bv /\ YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 SHADOW_OFF.
Proof.
intros ly S U W regs mem md ch ms HPRE HS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_put_string = ltac:(let v := eval vm_compute in STK_put_string in exact v)) by reflexivity.
unfold PS_FRAME_OWN, PS_SM_RET in *.
set (E := Ereg regs fs_extraT) in *.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl);
  unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (fsw_realign_facts (spZ regs - 192) ltac:(lia)
  ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
set (sp1 := 32 * ((spZ regs - 192) / 32)) in *.
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1).
{ exact (fsw_realign_val E ps_ss1 (restrict (w_H W) ms) 2%bv 2 (- 192) (spZ regs) HS
    ltac:(vm_compute; reflexivity) E2 ltac:(unfold spZ; apply u64_range) ltac:(lia)). }
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ps_ss1 ms 9%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 ?v => change (sr_get (ss_regs ps_ss1) 9%bv) with
    (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (- 192)) (SLit (-32))) (SLit 0)) end.
  rewrite denot_lit_U, U_SAlu. f_equal. cbn [zalu_raw]. rewrite U_SLit.
  assert (UA : YP0e.U E (SAlu ALU_AND (SOff 2 (- 192)) (SLit (-32))) = sp1).
  { unfold YP0e.U.
    rewrite (denot_and_m32 E 2 (spZ regs) (- 192) E2 ltac:(lia)
      ltac:(lia) ltac:(unfold spZ; apply u64_range)).
    apply wz. lia. }
  rewrite UA. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
split; [exact R2|]. split; [exact R9|]. split; [lia|]. split; [exact F2|].
split; [exact (fsw_reg_lit _ E _ ms 1%bv 548924 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_lit _ E _ ms 10%bv 64 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_lit _ E _ ms 12%bv 1 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl)|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ps_ss1 ms 23%bv HS).
change (sr_get (ss_regs ps_ss1) 23%bv) with (SOff 32 0). rewrite fsw_SOff0.
subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.
(* ---- the frame's SHADOW address, as the run computes it: s6 := (frame >> 3) + the shadow base. The engine's
   `addr_of` takes only an atom + offset, so the walk re-seats s6 on a fresh atom (FSW_K.fsw_reseat_atom) and gives
   that atom the frame's eight shadow bytes as a region. ---- *)
Definition PS_SH_STORE : Z := 0x860a4.   (* the first store through s6 (MEASURED) *)
Definition ps_ss_sh : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs fsw_ps_tbl FUEL PS_SH_STORE (ps_resume_ss PS_SM_RET)).
Definition ps_reseat47 (ss : sstate) : sstate :=
  add_atom (mkSS (ss_pc ss) (sr_set (ss_regs ss) 22%bv (SOff 47 0))
    (YP09.mkRegion (Some 47%nat) 0 8 0 8 [] :: ss_mem ss) (ss_resv ss) (ss_facts ss)) 47%nat (mkAF 0 (2 ^ 47) 0).
(* the state at the FIRST put call (the opening quote). MEASURED there: ra = PS_OPEN_RET, a0 = the out-object o
   (the resumed s3), a1 = PS_Q1 0x21240, a2 = 1 - the one-byte piece [34] of spieces_plain. *)
Definition ps_ss_put : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs fsw_ps_tbl FUEL A_put (ps_reseat47 ps_ss_sh)).

(* the shadow address of the frame is what the two instructions compute *)
Lemma ps_shadow_val : forall F, 0 <= F < 2 ^ 64 -> Z.shiftr F 3 + SHADOW_OFF = shadow_addr F.
Proof.
intros F HF. unfold shadow_addr. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.
(* a frame and its own shadow never overlap: in_app splits the application memory below the shadow or above it *)
Lemma ps_frame_sh_disj : forall F, in_app F 64 -> shadow_addr F + 8 <= F \/ F + 64 <= shadow_addr F.
Proof.
intros F (H4096 & [Hlo | (Hhi & Hceil)]); unfold shadow_addr, kLowShadowBeg, SHADOW_OFF, ASAN_CEIL in *;
  pose proof asan_consts as (C1 & _ & C3 & _); unfold kHighMemBeg in *;
  [right | left]; Z.div_mod_to_equations; lia.
Qed.

(* ---- segment 1: from the grant's return PS_SM_RET to the FIRST put call at A_put. The frame header, the
   frame-pointer slot at 80 of the re-aligned stack and the frame's shadow granule are written here; nothing
   allocates, so the journal only grows by the run's own writes. ---- *)
Lemma ps_seg1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc S2 U (W : world tfibsegs) mem2 md2 k pos sp1 regs2 X
  (Q : world tfibsegs -> config -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc S2 U W mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 X) (ps_resume_ss PS_SM_RET)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 PS_SM_RET) mem2 (seg_rom tfibsegs))) ->
  In (0, pos) (frames S2) ->
  bv_unsigned (ew (Ereg regs2 X) 8) = sp0 -> bv_unsigned (ew (Ereg regs2 X) 9) = sp1 ->
  bv_unsigned (ew (Ereg regs2 X) 10) = frame_addr lyc 0 pos ->
  ew (Ereg regs2 X) 32 = Z_to_bv 64 SHADOW_OFF ->
  sp0 - STK <= sp1 -> sp1 + 88 <= sp0 -> 104 <= STK ->
  (forall ms mat,
     st_ok tfibsegs (ewset (Ereg regs2 X) 47 (Z_to_bv 64 (shadow_addr (frame_addr lyc 0 pos)))) ps_ss_put
       (restrict (w_H W) ms) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md2) mat md2) k ->
     ARU tfibsegs B lyc S2 U W (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) ->
     (* the two runs write only the caller's saved words, the re-aligned frame, the fake frame and its shadow *)
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 104 <= a < sp0) -> ~ (sp1 <= a < sp1 + 88) ->
        ~ (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64) ->
        ~ (shadow_addr (frame_addr lyc 0 pos) <= a < shadow_addr (frame_addr lyc 0 pos) + 8) ->
        ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md2) mat md2)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 PS_SM_RET) mem2 (seg_rom tfibsegs)) md2) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc S2 U W mem2 md2 k pos sp1 regs2 X Q
  HJ HARU HS Hin E8 E9 E10 E32 Hwin Hsp88 HSTK Kont.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B lyc S2 U W mem2 md2 HARU) as HAR2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16s & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H47s & _ & Htop0 & Htop20).
destruct (al_frames _ _ LAWS lyc S2 W (unpoison U mem2) md2 0 pos HAR2 Hin) as (Hal32 & _ & Hfp & Hshp).
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (unpoison U mem2) md2 0 pos HAR2 Hin) as (H4096 & Hfc & Hfapp).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
set (F := frame_addr lyc 0 pos) in *.
assert (HFhi : F + 64 <= alloc_ceiling) by (rewrite Hfb in Hfc; exact Hfc).
(* ---- run 1: PS_SM_RET to the first store through the frame's shadow address ---- *)
fsw_aj_run_toU fsw_ps_tbl_ok HS HJ HARU PS_SH_STORE.
{ cbn [ss_mem ps_resume_ss ps_resume_regions].
  eapply awr_ok_cons_stack with (n := 8%nat); [reflexivity | exact E8 | cbn; lia | cbn; lia|].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - sp0);
    [reflexivity | rewrite E9; lia | cbn; lia | cbn; lia|].
  eapply awr_ok_cons_gen with (k := 10%nat) (b := F); [reflexivity | exact E10 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
  left; right; right; right. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr; cbn [fst snd]; rewrite ?Hfb; lia. }
rename HF into HFa.
(* ---- the machine value of s6, and the re-seat of the frame's shadow on atom 47 ---- *)
assert (E32u : bv_unsigned (ew (Ereg regs2 X) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
assert (Rsh : YK11.getr (ms_regs ms) 22%bv = Z_to_bv 64 (shadow_addr F)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) (Ereg regs2 X) ps_ss_sh ms 22%bv HS).
  change (sr_get (ss_regs ps_ss_sh) 22%bv)
    with (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)).
  rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U_SOff, U_SLit, U_SOff, E10, E32u, !Z.add_0_r.
  rewrite (zcanon_id F) by (unfold M64; lia).
  rewrite (zcanon_id 3) by (unfold M64; lia).
  change (Z.land 3 63) with 3.
  assert (Hdiv : 0 <= Z.shiftr F 3 < M64)
    by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; unfold M64; Z.div_mod_to_equations; lia).
  rewrite (zcanon_id _ Hdiv).
  rewrite <- (ps_shadow_val F ltac:(lia)).
  apply zcanon_id. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold M64, SHADOW_OFF in *. Z.div_mod_to_equations; lia. }
(* the three obligations of the re-seat, then the second run to the put call *)
assert (Hsh0 : 0 <= shadow_addr F /\ shadow_addr F + 8 <= 2 ^ 47)
  by (unfold shadow_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia).
assert (Hok : region_ok tfibsegs (ewset (Ereg regs2 X) 47 (Z_to_bv 64 (shadow_addr F)))
  (mrestrict (w_H W) (ms_mem ms)) (YP09.mkRegion (Some 47%nat) 0 8 0 8 [])).
{ pose proof (ARU_AR tfibsegs B lyc S2 U W (ms_mem ms) _ HARU) as HARrun.
  destruct (al_frames _ _ LAWS lyc S2 W (unpoison U (ms_mem ms)) _ 0 pos HARrun Hin)
    as (_ & _ & _ & Hshp').
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite ew_ewset_same, (wz (shadow_addr F) ltac:(lia)).
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros q Hq. apply (apresent_writable tfibsegs).
  destruct (Hshp' q ltac:(rewrite Hfb; change (64 / 8) with 8; lia)) as (Hp & Hno).
  exact (fsw_apresent_notowned B lyc S2 U W (ms_mem ms) _ (shadow_addr F + q) HARU ltac:(lia) Hno Hp). }
assert (Hdj : all_disjoint (ewset (Ereg regs2 X) 47 (Z_to_bv 64 (shadow_addr F)))
  (YP09.mkRegion (Some 47%nat) 0 8 0 8 []) (ss_mem ps_ss_sh)).
{ apply all_disjoint_of_extents.
  let v := eval vm_compute in (ss_mem ps_ss_sh) in change (ss_mem ps_ss_sh) with v.
  unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite ew_ewset_same, (wz (shadow_addr F) ltac:(lia)),
    (ew_ewset_other (Ereg regs2 X) 47 _ 8 ltac:(discriminate)),
    (ew_ewset_other (Ereg regs2 X) 47 _ 9 ltac:(discriminate)),
    (ew_ewset_other (Ereg regs2 X) 47 _ 10 ltac:(discriminate)), E8, E9, E10.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (ps_frame_sh_disj F Hfapp) as Hfs.
  unfold shadow_addr, SHADOW_OFF in *.
  destruct Hfs as [Hfs | Hfs];
  repeat match goal with |- _ /\ _ => split end; try exact I;
    first [left; Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia]. }
assert (Haf : afact_ok (ewset (Ereg regs2 X) 47 (Z_to_bv 64 (shadow_addr F))) 47 (mkAF 0 (2 ^ 47) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite ew_ewset_same, (wz (shadow_addr F) ltac:(lia)), Z.pow_0_r.
  split; [lia | split; [apply Z.mod_1_r | lia]]. }
pose proof (fsw_reseat_atom (Ereg regs2 X) ps_ss_sh (restrict (w_H W) ms) 22%bv 47 0 8 (mkAF 0 (2 ^ 47) 0)
  HS ltac:(vm_compute; reflexivity) ltac:(discriminate) ltac:(vm_compute; reflexivity)) as HR.
cbn [ms_regs ms_mem restrict] in HR. rewrite Rsh in HR.
pose proof (HR Hok Hdj Haf) as HS2. clear HR Hok Hdj Haf.
change (add_atom (mkSS (ss_pc ps_ss_sh) (sr_set (ss_regs ps_ss_sh) 22%bv (SOff 47 0))
  (YP09.mkRegion (Some 47%nat) 0 8 0 8 [] :: ss_mem ps_ss_sh) (ss_resv ps_ss_sh) (ss_facts ps_ss_sh))
  47%nat (mkAF 0 (2 ^ 47) 0)) with (ps_reseat47 ps_ss_sh) in HS2.
(* ---- run 2: the frame header and the shadow granule, up to the put of the opening quote ---- *)
fsw_aj_run_toU fsw_ps_tbl_ok HS2 HJ HARU A_put.
{ unfold ps_reseat47, add_atom. cbn [ss_mem].
  eapply awr_ok_cons_gen with (k := 47%nat) (b := shadow_addr F);
    [reflexivity | rewrite ew_ewset_same; apply wz; lia | | ].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    left; right; right; right. exists 0, pos. split; [left; reflexivity|]. right.
    unfold in_zr; cbn [fst snd]; rewrite ?Hfb; fold F; change (64 / 8) with 8; lia.
  - let v := eval vm_compute in (ss_mem ps_ss_sh) in change (ss_mem ps_ss_sh) with v.
    eapply awr_ok_cons_stack with (n := 8%nat);
      [reflexivity | rewrite (ew_ewset_other _ 47 _ 8 ltac:(discriminate)); exact E8 | cbn; lia | cbn; lia|].
    eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - sp0);
      [reflexivity | rewrite (ew_ewset_other _ 47 _ 9 ltac:(discriminate)), E9; lia
      | cbn; lia | cbn; lia|].
    eapply awr_ok_cons_gen with (k := 10%nat) (b := F);
      [reflexivity | rewrite (ew_ewset_other _ 47 _ 10 ltac:(discriminate)); exact E10 | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    left; right; right; right. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr; cbn [fst snd]; rewrite ?Hfb; lia. }
(* the write-set bound: run 1's regions are the saved words at s0, the re-aligned frame and the fake frame;
   run 2 adds the frame's shadow at atom 47. Nothing else is written. *)
apply (Kont _ _ HS2 HJ HARU).
intros a Ha H104 H88 HFr64 HSh8.
rewrite (HF (Z_to_bv 64 a)); [apply HFa | ].
- rewrite (wz a Ha). intros (rr & Hinr & Hrr).
  unfold ps_resume_ss, ps_resume_regions in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr;
    rewrite ?E8, ?E9, ?E10 in Hrr; lia.
- rewrite (wz a Ha). intros (rr & Hinr & Hrr).
  unfold ps_reseat47, add_atom in Hinr. cbn [ss_mem In] in Hinr.
  let v := eval vm_compute in (ss_mem ps_ss_sh) in change (ss_mem ps_ss_sh) with v in Hinr.
  cbn [In] in Hinr.
  destruct Hinr as [<-|[<-|[<-|[<-|[]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr;
    rewrite ?ew_ewset_same,
      ?(ew_ewset_other (Ereg regs2 X) 47 (Z_to_bv 64 (shadow_addr F)) 8 ltac:(discriminate)),
      ?(ew_ewset_other (Ereg regs2 X) 47 (Z_to_bv 64 (shadow_addr F)) 9 ltac:(discriminate)),
      ?(ew_ewset_other (Ereg regs2 X) 47 (Z_to_bv 64 (shadow_addr F)) 10 ltac:(discriminate)) in Hrr;
    rewrite ?E8, ?E9, ?E10, ?(wz (shadow_addr F)) in Hrr; lia.
Qed.

(* ================= the epilogue ================= *)
(* MEASURED: from put #3's return PS_CLOSE_RET one symbolic run reaches the final `ret` (stop SR_jalr at the saved
   ra atom), writing: the frame's shadow granule to 0xf5 (the frame is retired), the retired magic 0x45e0360e at
   the frame's first word, and the fake frame's FLAG byte to 0 - the store that releases the frame, which is
   fsw_flag_storeU's site. The saved registers are restored and sp is back at the entry sp. *)
Definition PS_CLOSE_RET : Z := 0x862b4.
Definition ps_hdr_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 8 (CVal 8 (SLit 74709));
   YP09.mkChunk 16 (CVal 8 (SLit 548808)); YP09.mkChunk 56 (CVal 8 (SOff (xatom 13) 0))].
Definition ps_fsh_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SLit 241)); YP09.mkChunk 1 (CVal 1 (SLit 241));
   YP09.mkChunk 2 (CVal 1 (SLit 241)); YP09.mkChunk 3 (CVal 1 (SLit 241));
   YP09.mkChunk 4 (CVal 1 (SLit 248)); YP09.mkChunk 5 (CVal 1 (SLit 243));
   YP09.mkChunk 6 (CVal 1 (SLit 243)); YP09.mkChunk 7 (CVal 1 (SLit 243))].
(* the state at PS_CLOSE_RET: the saved words at the s0 atom 8, the frame-pointer slot at atom 9, the frame at
   atom 24 (s5 = s8), its shadow at atom 47 (s6), its flag byte at the flag atom xatom 13; s7 = the shadow base *)
Definition ps_epi_ss (r : Z) : sstate :=
  mkSS r (sr_set (sr_set (sr_set sr_atoms 23%bv (SOff 32 0)) 21%bv (SOff 24 0)) 22%bv (SOff 47 0))
    [YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 ps_sv_chunks;
     YP09.mkRegion (Some 9%nat) 0 88 0 88 [YP09.mkChunk 80 (CVal 8 (SOff 24 0))];
     YP09.mkRegion (Some 24%nat) 0 64 0 64 ps_hdr_chunks;
     YP09.mkRegion (Some 47%nat) 0 8 0 8 ps_fsh_chunks;
     YP09.mkRegion (Some (xatom 13)) 0 1 0 1 []]
    None
    (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 88) 5);
              (24%nat, mkAF 4096 (2 ^ 47 - 64) 5); (47%nat, mkAF 0 (2 ^ 47) 0);
              (xatom 13, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).

(* ---- the SHARED shape of the state at the return of each of the three put calls (PS_OPEN_RET, PS_END_RET,
   PS_CLOSE_RET). After a call every register is its own atom (the kit's resume is sr_atoms), so the walk re-seats
   the three registers whose atom is named by a region: s7 = x23 = the shadow base (atom 32), s5 = x21 and
   s8 = x24 = the fake frame (atom 24), s6 = x22 = the frame's shadow (atom 47). The regions are the caller's saved
   words at s0 (atom 8), the re-aligned stack frame (atom 9) with the slots `scs` written so far, the fake frame
   (atom 24) with its header, the frame's eight shadow bytes (atom 47) and the frame's flag byte (xatom 13), then
   the walk's extra regions `rs` (the scanned string at atom 18 (image B: s2 = x18 holds s) between the first two calls, nothing at the third).
   ps_epi_ss PS_CLOSE_RET is this shape at scs = [the frame slot at +80] and rs = []. ---- *)
Definition PS_END_RET : Z := 0x862a0.     (* put #2's return (the run of bytes) *)
Definition ps_ret_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 23%bv (SOff 32 0)) 21%bv (SOff 24 0)) 22%bv (SOff 47 0).
Definition ps_ret_atoms (L : Z) : list (nat * afact) :=
  [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 88) 5);
   (24%nat, mkAF 4096 (2 ^ 47 - 64) 5); (47%nat, mkAF 0 (2 ^ 47) 0);
   (xatom 13, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (18%nat, mkAF 4096 (2 ^ 47 - (L + 1)) 0)].
(* the scanned string, read-only (the walk never writes it): [s, s + L + 1), the terminating zero included *)
Definition ps_str_region (L : Z) : YP09.region := YP09.mkRegion (Some 18%nat) 0 (L + 1) 0 0 [].
Definition ps_ret_regions (scs : list YP09.chunk) (rs : list YP09.region) : list YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 ps_sv_chunks ::
  YP09.mkRegion (Some 9%nat) 0 88 0 88 scs ::
  YP09.mkRegion (Some 24%nat) 0 64 0 64 ps_hdr_chunks ::
  YP09.mkRegion (Some 47%nat) 0 8 0 8 ps_fsh_chunks ::
  YP09.mkRegion (Some (xatom 13)) 0 1 0 1 [] :: rs.
Definition ps_ret_ss (r L : Z) (scs : list YP09.chunk) (rs : list YP09.region) : sstate :=
  mkSS r ps_ret_regs (ps_ret_regions scs rs) None (mkFacts (ps_ret_atoms L) [] []).
(* the frame-pointer slot the state carries at the opening put's return. Image A defines it in lib/A/ZZpsjoin.v; image
   B defines it here so that ZZpsclose's statements need only this file (ZZpsjoin imports it from here). *)
Definition psj_scs0 : list YP09.chunk := [YP09.mkChunk 80 (CVal 8 (SOff 24 0))].
Definition ps_epi_run : sstate * run_status :=
  Eval vm_compute in sym_runN tfibsegs fsw_ps_tbl FUEL (ps_epi_ss PS_CLOSE_RET).
Definition ps_epi_end : sstate := Eval vm_compute in fst ps_epi_run.

(* the epilogue's run, as fsw_flag_storeU asks for it: one sym_runN from PS_CLOSE_RET that performs the flag
   store and ends at the function's `ret` (RET_WORD_r at ps_epi_end's pc), which is where FSW_ret.fsw_retU closes
   the walk. Both facts are MEASURED (vm_compute) and proved here; they are the two non-trivial inputs of
   fsw_flag_storeU besides the journal. *)
Lemma ps_epi_run_eq :
  sym_runN tfibsegs fsw_ps_tbl FUEL (ps_epi_ss PS_CLOSE_RET) = (ps_epi_end, RS_stopped (SR_jalr (SOff (xatom 0) 0))).
Proof. vm_cast_no_check (eq_refl (sym_runN tfibsegs fsw_ps_tbl FUEL (ps_epi_ss PS_CLOSE_RET))). Qed.

Lemma ps_epi_ret_word : clookup fsw_ps_tbl (ss_pc ps_epi_end) = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.

(* the flag byte is 0 at the end of that run: the premise fsw_flag_storeU takes to know the frame was released *)
Lemma ps_epi_flag0 : forall E msr, st_ok tfibsegs E ps_epi_end msr ->
  forall fl, bv_unsigned (ew E (xatom 13)) = fl ->
  mbyte tfibsegs (ms_mem msr) fl = Some (Z_to_bv 8 0).
Proof.
intros E msr HS fl Hfl.
pose proof (fsw_region_nth E ps_epi_end msr 4 _ HS ltac:(vm_compute; reflexivity)) as HR.
pose proof (fsw_field E (ms_mem msr) (xatom 13) fl [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1%N (SLit 0) 0
  HR Hfl ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in HV.
pose proof (HV 0%nat ltac:(cbn; lia)) as Hb.
rewrite Z.add_0_r, Z.add_0_r in Hb. rewrite Hb. reflexivity.
Qed.

(* ================= the fake frame across a callee's journal =================
   put_string holds its class-0 fake frame across all three put calls, and the state at each return carries the
   frame's header, its eight shadow bytes and its flag byte (ps_ret_ss). No `kept` clause of the callee's post
   mentions them - they are not in the caller's stack window and not a block - so the bytes come from the CALLEE
   JOURNAL's frames clause (Reusable/YCbq.v:364-366), which keeps every byte of a frame of `frames Sc` and of its
   shadow that the callee's footprint misses. The clause reads the UNPOISONED memories, so each end needs the
   bridge below: the frame's own bytes lie in application memory (AR_frames_law's in_app) and its shadow bytes
   are not owned (the same law's fourth clause), so `unpoison` changes neither. ---- *)
Lemma ps_app_unpoison : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S U W mem md a HARU Ha Happ. unfold mbyte, mrestrict.
destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
rewrite (unpoison_out U mem (Z_to_bv 64 a)); [reflexivity|].
rewrite (wz a Ha). destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
destruct (ush_facts tfibsegs B ly S U W mem md a HARU E) as (_ & L1 & L2). unfold kHighMemBeg in *. lia.
Qed.

Lemma ps_fr_unpoison : forall ly S U (W : world tfibsegs) mem md cid pos a,
  ARU tfibsegs B ly S U W mem md -> In (cid, pos) (frames S) -> 0 <= cid ->
  (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
  mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S U W mem md cid pos a HARU Hin Hc0 Hr.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md cid pos HAR Hin) as (_ & Happ & _ & Hsp).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hin) as (H4096 & Hceil & _).
pose proof (fs_frame_bytes_pos cid Hc0) as Hfb.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (Hc1 & _).
destruct Hr as [Hr | Hr].
- apply (ps_app_unpoison ly S U W mem md a HARU);
    unfold in_app, kLowShadowBeg, ASAN_CEIL, SHADOW_OFF, kHighMemBeg in *; lia.
- destruct (Hsp (a - shadow_addr (frame_addr ly cid pos)) ltac:(lia)) as (_ & Hno).
  replace (shadow_addr (frame_addr ly cid pos) + (a - shadow_addr (frame_addr ly cid pos))) with a in Hno by lia.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(unfold ASAN_CEIL in *; lia)) as (S1 & S2).
  assert (Ha : 0 <= a < 2 ^ 64) by (unfold kLowMemEnd, kHighShadowEnd in *; lia).
  unfold mbyte, mrestrict. destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
  rewrite (fsw_unpoison_notowned B ly S U W mem md a HARU Ha Hno). reflexivity.
Qed.

(* the frame and its shadow keep every byte across a callee whose footprint misses them *)
Lemma ps_fr_kept : forall STKc sp1 FPc lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc cid pos a,
  ajournal tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  In (cid, pos) (frames Sc) -> 0 <= cid -> ~ inFP FPc a ->
  (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memc) a.
Proof.
intros STKc sp1 FPc lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc cid pos a
  HJ HARUc HARU' Hin Hc0 HnF Hr.
pose proof HJ as (_ & HLE & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & F4 & _).
destruct HLE as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfr; cbn [app]; exact Hin).
assert (HF : frame_addr ly' cid pos = frame_addr lyc cid pos)
  by (unfold frame_addr; rewrite HlyF; reflexivity).
rewrite <- (ps_fr_unpoison ly' S' U' W' mem' md' cid pos a HARU' Hin' Hc0 ltac:(rewrite HF; exact Hr)).
rewrite <- (ps_fr_unpoison lyc Sc Uc W memc mdc cid pos a HARUc Hin Hc0 Hr).
apply (mbyte_of_aview tfibsegs). apply (F4 cid pos a Hin); [|exact HnF].
destruct Hr as [Hr | Hr]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; lia.
Qed.

(* ================= the frame chain at the three put call sites =================
   put's fpreU asks for `achain lyc rd (spZ regsc) (s0Z regsc) ch1`. At each of put_string's three put calls the
   machine sp is the re-aligned sp1 and s0 is put_string's own entry sp, so the chain is the caller's chain with
   put_string's own record pushed on it - unless the entry sp sits in the top 16 bytes of the stack window, where
   `achain`'s first arm makes the chain empty. `ps_ch1` names both cases. ---- *)
Lemma ps_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  val_mem tfibsegs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview tfibsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Hb : forall k, (k < 8)%nat -> aview tfibsegs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Hb 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Hb 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Hb 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Hb 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Hb 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Hb 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Hb 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Hb 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

Definition ps_ch1 (ly : alayout) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list (Z * Z * Z) :=
  if ly_top ly - 16 <=? spZ regs then [] else (spZ regs, raZ regs, s0Z regs) :: ch.

Lemma ps_chain_put : forall ly S U (W : world tfibsegs) regs mem md ch (m' : word -> option byte) sp1,
  afn_preU tfibsegs B STK_put_string ly S U W regs mem md ch ->
  (forall a, spZ regs <= a < 2 ^ 64 ->
     aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) (unpoison U mem) a) ->
  rdword (aview tfibsegs (w_H W) m') (spZ regs - 8) = Some (raZ regs) ->
  rdword (aview tfibsegs (w_H W) m') (spZ regs - 16) = Some (s0Z regs) ->
  sp1 + 16 <= spZ regs ->
  achain ly (aview tfibsegs (w_H W) m') sp1 (spZ regs) (ps_ch1 ly regs ch).
Proof.
intros ly S U W regs mem md ch m' sp1 HPRE Hagree H8 H16 Hsp1.
pose proof HPRE as ((HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & Hqt) & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold ps_ch1. destruct (Z.leb_spec (ly_top ly - 16) (spZ regs)) as [Hle | Hlt].
- left. split; [right; left; exact Hle | reflexivity].
- exact (achain_push ly (aview tfibsegs (w_H W) (unpoison U mem)) (aview tfibsegs (w_H W) m')
    (spZ regs) (s0Z regs) (raZ regs) ch sp1 Hch ltac:(lia) Hagree H8 H16 Hra4 ltac:(lia)
    ltac:(lia) ltac:(lia) Hsp1).
Qed.


(* the two words the chain reads, out of the s0 region's saved-register chunks: ps_sv_chunks puts the saved ra
   at s0 - 8 (xatom 0) and the caller's own s0 at s0 - 16 (xatom 1) *)
Lemma ps_saved_words : forall E (H : word -> bool) (mem : word -> option byte) sp0 ra s0v,
  region_ok tfibsegs E (mrestrict H mem) (YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 ps_sv_chunks) ->
  bv_unsigned (ew E 8) = sp0 ->
  bv_unsigned (ew E (xatom 0)) = ra -> bv_unsigned (ew E (xatom 1)) = s0v ->
  0 <= ra < 2 ^ 64 -> 0 <= s0v < 2 ^ 64 ->
  rdword (aview tfibsegs H mem) (sp0 - 8) = Some ra /\
  rdword (aview tfibsegs H mem) (sp0 - 16) = Some s0v.
Proof.
intros E H mem sp0 ra s0v HR E8 E33 E34 Hra Hs0.
assert (D : forall n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hv Hr; rewrite fsw_SOff0, <- Hv; symmetry; apply Z_to_bv_bv_unsigned).
split.
- replace (sp0 - 8) with (sp0 + (- 8)) by ring.
  exact (ps_rdword_of_val_mem H mem _ ra
    (fsw_field E (mrestrict H mem) 8%nat sp0 ps_sv_chunks (-104) 0 (-104) 0 (-8) 8 (SOff (xatom 0) 0) ra
       HR E8 ltac:(vm_compute; tauto) (D (xatom 0) ra E33 Hra) ltac:(cbn [Z.of_N]; lia)
       ltac:(cbn [Z.of_N]; lia)) Hra).
- replace (sp0 - 16) with (sp0 + (- 16)) by ring.
  exact (ps_rdword_of_val_mem H mem _ s0v
    (fsw_field E (mrestrict H mem) 8%nat sp0 ps_sv_chunks (-104) 0 (-104) 0 (-16) 8 (SOff (xatom 1) 0) s0v
       HR E8 ltac:(vm_compute; tauto) (D (xatom 1) s0v E34 Hs0) ltac:(cbn [Z.of_N]; lia)
       ltac:(cbn [Z.of_N]; lia)) Hs0).
Qed.
(* ================= one put call, composed ================= *)
(* The three put calls of put_string (the opening quote at PS_OPEN_RET, the run of bytes at PS_END_RET, the
   closing quote at PS_CLOSE_RET) differ only in their arguments, so the composition is proved ONCE here and
   instantiated three times. put's contract is the callee hypothesis HPUT; the resume is the kit's raised-top
   after-call (put's post has window top ot, not the call sp: FSH_Fn_FORM 3a).
   NOTE (soundness rule, a Theorem Labs lane 01:03Z): this lemma uses a static-writing callee's spec, so over S0's
   pre-FP core it is 'built over S0's pre-FP core: not counted' until the walk is rebuilt over the FP-keyed
   core; the text carries over unchanged. *)
Lemma ps_put_call :
  forall STK sp0 FP own ly S U0 U W0 mem md (W : world tfibsegs) lyc Sc memc mdc k regsc off ch1 pos
         r oo src n buf cap failed (text bs : list Z) live peak cnt fail ot s0v lo hi cs extra
         (Q : world tfibsegs -> config -> Prop),
  (* the caller's journal at the call, and the facts the callee's fpreU needs *)
  (* the entry's heads U0 and the current heads U differ after a put that grows the buffer (uswap) *)
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U0 mem) md own lyc Sc W (unpoison U memc) mdc k ->
  ARU tfibsegs B lyc Sc U W memc mdc ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc) ->
  spZ regsc = sp0 + off -> off mod 16 = 0 -> off <= 0 -> STK_put - off <= STK ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview tfibsegs (w_H W) (unpoison U memc)) (spZ regsc) (s0Z regsc) ch1 ->
  (* put's own premises, at the call *)
  (* NO CTX row and no CTX binder: the writer specs dropped both (S0 794d06a106b, owner-approved on a Theorem Labs lane's proof
     that the row is unsatisfiable in a reachable state; the binder by owner ruling 05:05Z). *)
  fs_heads B lyc Sc U ->
  Z.of_nat (length (frames Sc)) <= FRL_CRT_CALLEE + 1 ->
  getr regsc 10 = w64 oo -> getr regsc 11 = w64 src -> getr regsc 12 = w64 n ->
  FSH_Fn_writer.wout_ok B tfibsegs lyc Sc W memc oo buf cap failed text ->
  fs_glob tfibsegs W memc live peak cnt fail ->
  (* the live buffer's head is user-poisoned (put_spec's premise, a Theorem Labs lane 2026-10-29) *)
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  spZ regsc <= oo -> oo + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top lyc ->
  (oo = spZ regsc + 8 /\ raZ regsc < alloc_ceiling \/
   spZ regsc + 16 <= oo /\ exists ra nfp,
     rdword (aview tfibsegs (w_H W) (unpoison U memc)) (oo - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W) (unpoison U memc)) (oo - 16) = Some nfp /\
     (ra < 4096 \/ nfp < alloc_ceiling)) ->
  (forall a, spZ regsc <= a < ot -> apresent (w_H W) memc a) ->
  zbytes_at tfibsegs W memc src bs -> FSH_Fn_writer.wsrc_kept B tfibsegs lyc Sc U W memc buf src bs ->
  Z.of_nat (length bs) = n -> WriterSpec.bytes_ok bs ->
  0 <= src /\ src + n <= alloc_ceiling -> (src + n <= oo \/ ot <= src) ->
  Z.of_nat (length text) + n + 1 <= FSH_Fn_writer.WMAX -> cap <= FSH_Fn_writer.WMAX -> cap <= live ->
  FSH_Fn_writer.wbudget_pre Sc cap cnt live (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) ->
  (* the resume: the caller's saved words at s0v, and the footprint relation *)
  getr regsc 1 = w64 r ->
  (forall regs', aregs_preserved regsc regs' -> YK11.getr regs' 8%bv = Z_to_bv 64 s0v) ->
  s0v mod 16 = 0 -> s0v <= sp0 -> sp0 - STK <= s0v + lo -> lo <= hi -> hi <= 0 ->
  sp0 - STK <= ot - (STK_put + (ot - spZ regsc)) -> ot <= sp0 -> spZ regsc <= ot ->
  regions_wf [fs_ret_s0_region lo hi cs] = true ->
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  (forall regs', Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) memc) s0v) cs) ->
  spZ regsc <= s0v + lo -> s0v + hi <= ot -> (s0v + hi <= oo \/ oo + 32 <= s0v + lo) ->
  (* the four-arm footprint relation FSW_frame3.fsw_after_callU_s0_ot takes (put's FP is the statics and the
     buffer block: never a byte of a frame of the entry frames S, so FSW_K3.fsw_fp_sub's fifth arm is not needed) *)
  (forall a, inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (inFP FP a /\ in_img tfibsegs a) \/
     in_frames lyc own a) ->
  (* the caller's own class-0 fake frame, live across the call: the callee's footprint misses it and its shadow,
     so the callee journal's frames clause keeps every byte of both (ps_fr_kept) *)
  In (0, pos) (frames Sc) ->
  (forall a, (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + fs_frame_bytes 0 \/
              shadow_addr (frame_addr lyc 0 pos) <= a
                < shadow_addr (frame_addr lyc 0 pos) + fs_frame_bytes 0 / 8) ->
     ~ inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a) ->
  (* the continuation, with put's model result and the resumed state *)
  (forall (st' : WriterApp.wst) buf' U' ly' S' W' regs' mem' md',
     st' = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs ->
     FSH_Fn_writer.uswap U U' buf buf' cap ->
     ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U0 mem) md own ly' S' W' (unpoison U' mem') md'
       (k + FSH_Fn_writer.wevk cap st') ->
     ARU tfibsegs B ly' S' U' W' mem' md' ->
     aregs_preserved regsc regs' ->
     FSH_Fn_writer.wout_ok B tfibsegs ly' S' W' mem' oo buf' (WriterApp.w_cap st') (WriterApp.w_failed st')
       (WriterApp.w_text st') ->
     FSH_Fn_writer.wbudget_kept Sc S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') ->
     FSH_Fn_writer.bswap (ablocks B lyc Sc) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') ->
     wkeep tfibsegs W W' memc mem' (spZ regsc) ot oo 32 ->
     (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
        fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st' - cap) peak'
          (WriterApp.w_cnt st') (WriterApp.w_fail st')) ->
     (forall i, 0 <= i < n -> mbyte tfibsegs (mrestrict (w_H W') mem') (src + i)
                            = mbyte tfibsegs (mrestrict (w_H W) memc) (src + i)) ->
     (forall a, (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + fs_frame_bytes 0 \/
                 shadow_addr (frame_addr lyc 0 pos) <= a
                   < shadow_addr (frame_addr lyc 0 pos) + fs_frame_bytes 0 / 8) ->
        mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memc) a) ->
     st_ok tfibsegs (Ereg regs' extra) (fss_ret_s0 r lo hi cs)
       (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regsc memc mdc) Q.
Proof.
intros STK sp0 FP own ly S U0 U W0 mem md W lyc Sc memc mdc k regsc off ch1 pos r oo src n buf cap failed text bs
  live peak cnt fail ot s0v lo hi cs extra Q
  HJ HARU HRO Hsp Hal Hneg Hbud Hra Hra4 Hgp Htp Hch Hheads Hfr G10 G11 G12 HOUT HGLOB HHEAD Hspo Hoot Hot16
  Hottop Hchain HPRESENT Hz Hsrck Hlen Hbok Hs0n Hsep Hwmax Hcap Hlive Hbp
  Hr Hs0r Hs0al Hs0top Hs0lo Hlohi Hhi0 Hwinc Hotsp Hspot Hwf Hin Hcs Hlo1 Hhi1 Hdisj HFP HFRin HFRfp Kont.
(* put's precondition from the caller's journal (FSW_ret.fsw_fpreU_atFP) *)
pose proof (fsw_fpreU_atFP B STK sp0 FP ly S U W0 (unpoison U0 mem) md own lyc Sc W memc mdc k regsc STK_put off ch1
  HJ HARU HRO Hsp Hal Hneg ltac:(vm_compute; discriminate) Hbud Hra Hra4 Hgp Htp Hch) as HPREc.
eapply SRr_bind;
  [exact (HPUT lyc Sc U W regsc memc mdc ch1 ot oo src n buf cap failed text bs live peak cnt fail
     HPREc Hheads Hfr G10 G11 G12 HOUT HGLOB HHEAD Hspo Hoot Hot16 Hottop Hchain HPRESENT Hz Hsrck Hlen Hbok
     Hs0n Hsep Hwmax Hcap Hlive Hbp) |].
cbv beta. intros W' c' Hwle (st' & buf' & U' & Hst' & Hsw & HPOST).
unfold FSH_Fn_writer.wpost, fpostU in HPOST.
destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ).
destruct HQ as (HOUT' & HBK & HBS & HKEEP & HPK & HSRC').
rewrite Hr in Ec. unfold w64 in Ec.
destruct (fsw_after_callU_s0_ot B STK sp0 FP ly S U0 W0 mem md own lyc Sc U W memc mdc k
  (STK_put + (ot - spZ regsc)) (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) ot regsc
  ly' S' U' W' regs' mem' md'
  (FSH_Fn_writer.wevk cap st') extra cs r lo hi s0v
  HJ HJc OK' PO' HFP HP ltac:(lia) (Hs0r regs' HP) Hs0al ltac:(lia) ltac:(lia) Hs0lo Hlohi Hhi0 Hs0top
  Hwf Hin (Hcs regs')
  ltac:(intros a Ha; destruct (HKEEP a ltac:(lia) ltac:(destruct Hdisj; lia)) as [Hm _]; exact Hm))
  as (HJ2 & HS2).
assert (HARU2 : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
subst c'.
exact (Kont st' buf' U' ly' S' W' regs' mem' md' Hst' Hsw HJ2 HARU2 HP HOUT' HBK HBS HKEEP HPK HSRC'
  (fun a Ha => ps_fr_kept (STK_put + (ot - spZ regsc)) ot
     (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) lyc Sc U W memc mdc ly' S' U' W' mem' md'
     (FSH_Fn_writer.wevk cap st') 0 pos a HJc HARU HARU2 HFRin ltac:(lia) (HFRfp a Ha) Ha)
  HS2).
Qed.

(* ================= from the entry to the FIRST put call, through the fake-frame grant ================= *)
(* ps_seg0 to the __asan_stack_malloc_0 call, the kit's fsw_stack_malloc_atU across it, ps_resume_sm to rebuild the
   state at its return, and ps_seg1 to the opening-quote put. Uses no callee contract: only the runtime's laws and
   astack_malloc_realizesU (named Section hypotheses above). *)
Lemma ps_to_put1 : forall ly S U (W : world tfibsegs) regs mem md ch FP (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_put_string ly S U W regs mem md ch ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  (forall pos S2 regs2 md2 ms mat,
     frames S2 = (0, pos) :: frames S -> ablocks B ly S2 = ablocks B ly S ->
     st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
     YK11.getr regs2 8%bv = YK11.getr regs 2%bv ->
     YK11.getr regs2 9%bv = Z_to_bv 64 (32 * ((spZ regs - PS_FRAME_OWN) / 32)) ->
     (* the machine sp at the call is the re-aligned sp1, and s5 = s8 = the fake frame: ps_put_call's
        `spZ regsc = sp0 + off` and ps_inv's x21 / x24 read these (a Theorem Labs lane's finding, 2026-10-29) *)
     YK11.getr regs2 2%bv = Z_to_bv 64 (32 * ((spZ regs - PS_FRAME_OWN) / 32)) ->
     YK11.getr regs2 10%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
     YK11.getr regs2 19%bv = YK11.getr regs 10%bv -> YK11.getr regs2 18%bv = YK11.getr regs 11%bv ->
     YK11.getr regs2 3%bv = YK11.getr regs 3%bv -> YK11.getr regs2 4%bv = YK11.getr regs 4%bv ->
     st_ok tfibsegs (ewset (Ereg regs2 (fs_extraT ++ ps_xs regs (flag_addr ly 0 pos))) 47
                       (Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos))))
       ps_ss_put (restrict (w_H W) ms) ->
     ajournal tfibsegs B STK_put_string (spZ regs) FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md2) mat md2) 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) ->
     (* the stretch writes no live block and no image byte. The journal above does not say so - put_string's own
        FP holds the writer's buffer and fs's allocator statics, which the journal's block and image clauses
        except - but the three runs and the runtime's grant do: the runs write only put_string's stack window,
        its fake frame and that frame's shadow, and the grant keeps every block byte and every image byte
        (acall_kept). This is what carries wout_ok, fs_glob, cstr_ok and wsrc_kept over the prologue. *)
     (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
        aview tfibsegs (w_H W) (unpoison U (ms_mem ms)) (b + i)
          = aview tfibsegs (w_H W) (unpoison U mem) (b + i)) ->
     (forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
        ~ (as_errno B <= a < as_errno B + 4) ->
        aview tfibsegs (w_H W) (unpoison U (ms_mem ms)) a = aview tfibsegs (w_H W) (unpoison U mem) a) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md2) mat md2)) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put_string regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP Q HPRE Hfr Kont.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_put_string = ltac:(let v := eval vm_compute in STK_put_string in exact v)) by reflexivity.
apply (ps_seg0 ly S U W regs mem md ch FP Q HPRE).
intros ms mat HS HJ HARU HF HFr.
destruct (ps_sm_site ly S U W regs mem md ch ms HPRE HS)
  as (R2 & R9 & Rsp1 & Rsp32 & R1 & R10 & R12 & R3 & R4 & R8 & R23).
set (sp0 := spZ regs) in *. set (sp1 := 32 * ((sp0 - PS_FRAME_OWN) / 32)) in *.
unfold PS_FRAME_OWN in *.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 19%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R19.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 18%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R18.
assert (Hspc : spZ (ms_regs ms) = sp0 + (sp1 - sp0)) by (unfold spZ at 1; rewrite R2, wz by lia; lia).
assert (Hoff16 : (sp1 - sp0) mod 16 = 0) by (unfold sp1; Z.div_mod_to_equations; lia).
(* the config at the stack_malloc call *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (Ereg regs fs_extraT) _ ms HS eq_refl).
change (ss_pc ps_ss1) with PC_stack_malloc_0. rewrite <- HSMPC.
eapply SRr_bind;
  [exact (fsw_stack_malloc_atU B HENV HML HSMP 0 HSM0 ltac:(lia) W (ms_regs ms) (ms_mem ms) STK_put_string sp0 FP
     ly S W (unpoison U mem) md [] ly S U (with_vm_backing (m_vm_lazy md) mat md) 0 (sp1 - sp0)
     (Z_to_bv 64 PS_SM_RET) HJ HARU Hspc Hoff16
     ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite R3; destruct HPRE as ((_ & _ & _ & Hgp & _) & _); exact Hgp)
     ltac:(rewrite R4; destruct HPRE as ((_ & _ & _ & _ & Htp & _) & _); exact Htp)
     R1 ltac:(apply ret_ok_even; rewrite unsigned_lit_small by (unfold PS_SM_RET; lia); reflexivity)
     (ps_grant (frames S) Hfr)) |].
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HARU2 & HP & H10 & Hab & Hfrs & Hfresh
  & Hnev & Hbb & Hz & Hflag & Hkept).
(* the resumed registers *)
assert (P8 : YK11.getr regs2 8%bv = YK11.getr (ms_regs ms) 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : YK11.getr regs2 9%bv = YK11.getr (ms_regs ms) 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P23 : YK11.getr regs2 23%bv = YK11.getr (ms_regs ms) 23%bv) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
assert (P19 : YK11.getr regs2 19%bv = YK11.getr (ms_regs ms) 19%bv) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
assert (P18 : YK11.getr regs2 18%bv = YK11.getr (ms_regs ms) 18%bv) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
assert (P3 : YK11.getr regs2 3%bv = YK11.getr (ms_regs ms) 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : YK11.getr regs2 4%bv = YK11.getr (ms_regs ms) 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (E8 : YK11.getr regs2 8%bv = Z_to_bv 64 sp0)
  by (rewrite P8, R8; unfold sp0, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E9 : YK11.getr regs2 9%bv = Z_to_bv 64 sp1) by (rewrite P9, R9; reflexivity).
assert (P2 : YK11.getr regs2 2%bv = YK11.getr (ms_regs ms) 2%bv)
  by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (E2 : YK11.getr regs2 2%bv = Z_to_bv 64 sp1) by (rewrite P2, R2; reflexivity).
assert (E10 : YK11.getr regs2 10%bv = Z_to_bv 64 (frame_addr ly 0 pos)) by exact H10.
assert (E23 : YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF) by (rewrite P23, R23; reflexivity).
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
(* the saved words: the call-site state's stack chunks, read in the resume env *)
assert (Hcs : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ ps_xs regs (flag_addr ly 0 pos)))
                       (mrestrict (w_H W) (ms_mem ms)) sp0) ps_sv_chunks).
{ pose proof (fsw_region_nth (Ereg regs fs_extraT) ps_ss1 (restrict (w_H W) ms) 0 _ HS ltac:(vm_compute; reflexivity)) as HR0.
  cbn [ms_mem restrict] in HR0. destruct HR0 as (_ & _ & _ & Hck).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hck.
  rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl) in Hck. fold sp0 in Hck.
  unfold ps_sv_chunks. cbn [map seq].
  repeat (apply Forall_cons; [|]); [..|apply Forall_nil].
  all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?xa 0))) =>
    let c := eval vm_compute in (find (fun c => YP09.c_off c =? o) (YP09.r_chunks (nth 0 (ss_mem ps_ss1) (YP09.mkRegion None 0 0 0 0 [])))) in
    lazymatch c with Some (YP09.mkChunk _ (CVal _ ?v1)) =>
      apply (ps_chunk_transfer (Ereg regs fs_extraT) _ _ _ o 8 v1);
      [ rewrite !fsw_SOff0; unfold xatom; cbn [Nat.add];
        first [ rewrite (ew_Ereg_extra regs2 _ 0); cbn
              | idtac ];
        try (rewrite ew_Ereg_extra; cbn [nth fs_extraT ps_xs app]);
        try (rewrite (ew_Ereg_nat regs fs_extraT _ _ eq_refl)); reflexivity
      | apply (proj1 (Forall_forall _ _) Hck); vm_compute; tauto ]
    end end. }
replace (sp0 + (sp1 - sp0) - ESTACK) with (sp1 - ESTACK) in Hkept by lia.
replace (sp0 + (sp1 - sp0)) with sp1 in Hkept by lia.
pose proof (ps_resume_sm STK_put_string sp0 FP ly S W (unpoison U mem) md [] ly S S2 U W (ms_mem ms)
  (with_vm_backing (m_vm_lazy md) mat md) mem2 md2 0 pos sp1 regs regs2 HJ2 HARU2 HARU Hkept Hin E8 E9 E10 E23
  Hflag ltac:(lia) ltac:(lia) H47 Hal16 Rsp32 Hcs) as HS2.
set (X := fs_extraT ++ ps_xs regs (flag_addr ly 0 pos)) in *.
assert (U8 : bv_unsigned (ew (Ereg regs2 X) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs2 X 8 8%bv eq_refl), E8; apply wz; lia).
assert (U9 : bv_unsigned (ew (Ereg regs2 X) 9) = sp1)
  by (rewrite (ew_Ereg_nat regs2 X 9 9%bv eq_refl), E9; apply wz; lia).
assert (U10 : bv_unsigned (ew (Ereg regs2 X) 10) = frame_addr ly 0 pos).
{ rewrite (ew_Ereg_nat regs2 X 10 10%bv eq_refl), E10. apply wz.
  pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
  destruct (frames_bounds tfibsegs B (AR_laws_ok tfibsegs B) ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin)
    as (H4096 & Hfc & _).
  assert (Hfb0 : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb0 in Hfc. lia. }
assert (U32 : ew (Ereg regs2 X) 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold X; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
apply (ps_seg1 STK_put_string sp0 FP ly S W (unpoison U mem) md [] ly S2 U W mem2 md2 0 pos sp1 regs2 X Q
  HJ2 HARU2 HS2 Hin U8 U9 U10 U32 ltac:(lia) ltac:(lia) ltac:(lia)).
intros ms' mat' HS3 HJ3 HARU3 Hkeep1.
(* the two keep clauses: hop 1 the prologue run (it writes only [sp0 - 192, sp0)), hop 2 the runtime's grant
   (acall_kept keeps every block byte and every image byte), hop 3 ps_seg1's write-set bound *)
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin)
  as (HF4096 & HFce & _).
assert (Hfb0 : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb0 in HFce.
pose proof (shadow_addr_bounds (frame_addr ly 0 pos) ltac:(unfold ASAN_CEIL in *; lia)) as (HSh1 & HSh2).
cbn [ms_mem mkst] in HF.
assert (HOP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 192 <= a < sp0) ->
  ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hout. apply HF. rewrite (wz a Ha). intros (rr & Hinr & Hrr).
  let v := eval vm_compute in (ss_mem ps_ss0) in change (ss_mem ps_ss0) with v in Hinr.
  cbn [In] in Hinr.
  destruct Hinr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr;
    rewrite ?(ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl) in Hrr;
    try change (bv_unsigned (YK11.getr regs 2%bv)) with sp0 in Hrr;
    unfold PS_FRAME_OWN in *; lia. }
apply (Kont pos S2 regs2 md2 ms' mat' Hfrs Hab Hnev Hbb
  (eq_trans E8 (eq_sym (eq_trans (eq_sym (Z_to_bv_bv_unsigned 64 (YK11.getr regs 2%bv))) eq_refl)))
  E9 E2 E10
  (eq_trans P19 R19) (eq_trans P18 R18) (eq_trans P3 R3) (eq_trans P4 R4)
  HS3 HJ3 HARU3).
- (* every live block byte is unchanged *)
  intros b m i Hinb Hi.
  destruct (al_blocks _ _ LAWS ly S2 W (unpoison U mem2) md2 b m HAR2 ltac:(rewrite Hab; exact Hinb))
    as (_ & Hb4096 & Hbce & Hbapp & _).
  pose proof (sep_block_frame tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 b m 0 pos HAR2
    ltac:(rewrite Hab; exact Hinb) Hin) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Hfb0 in Hsep.
  unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Hbapp.
  assert (Hnsh : ~ (shadow_addr (frame_addr ly 0 pos) <= b + i < shadow_addr (frame_addr ly 0 pos) + 8)).
  { pose proof ASAN_CEIL_range as (Hc1 & _).
    clear - HFce HF4096 Hbapp Hi Hc1.
    unfold shadow_addr, SHADOW_OFF, ASAN_CEIL in *. Z.div_mod_to_equations. lia. }
  transitivity (aview tfibsegs (w_H W) (unpoison U mem2) (b + i)).
  { apply aview_at. unfold unpoison.
    rewrite (Hkeep1 (b + i) ltac:(unfold ASAN_CEIL in *; lia) ltac:(unfold ASAN_CEIL in *; lia)
      ltac:(unfold ASAN_CEIL in *; lia) ltac:(lia) Hnsh).
    reflexivity. }
  transitivity (aview tfibsegs (w_H W) (unpoison U (ms_mem ms)) (b + i)).
  { exact (proj1 (proj2 Hkept) b m i Hinb Hi ltac:(intros [])). }
  { apply aview_at. unfold unpoison.
    rewrite (HOP1 (b + i) ltac:(unfold ASAN_CEIL in *; lia) ltac:(unfold ASAN_CEIL in *; lia)). reflexivity. }
- (* every image byte off the owned statics and off errno is unchanged *)
  intros a Hi Ho He.
  pose proof (fs_segs_img a Hi) as Hlow. unfold FS_IMG_END in Hlow.
  assert (Hnfr : ~ (frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64)).
  { intros Hfa. apply (frm_img tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos a HAR2 Hin);
      [rewrite Hfb0; exact Hfa | exact Hi]. }
  transitivity (aview tfibsegs (w_H W) (unpoison U mem2) a).
  { apply aview_at. unfold unpoison.
    rewrite (Hkeep1 a ltac:(lia) ltac:(unfold ASAN_CEIL in *; lia)
      ltac:(unfold ASAN_CEIL in *; lia) Hnfr ltac:(unfold kLowMemEnd in *; lia)).
    reflexivity. }
  transitivity (aview tfibsegs (w_H W) (unpoison U (ms_mem ms)) a).
  { exact (proj1 (proj2 (proj2 Hkept)) a Hi Ho He). }
  { apply aview_at. unfold unpoison.
    rewrite (HOP1 a ltac:(lia) ltac:(unfold ASAN_CEIL in *; lia)).
    reflexivity. }
Qed.

(* ---- the epilogue as one step: the flag store releases the fake frame (FSW_frame.fsw_flag_storeU over the whole
   run, which ends at the `ret`), then the function returns (FSW_ret.fsw_retU). The callee-saved registers at the
   `ret` are the thirteen saved words reloaded (atoms xatom 1 .. xatom 12), sp back at the entry sp (atom 8), gp / tp
   untouched. Uses no callee contract. ---- *)
Definition ps_epi_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 8 0 | 8 => SOff (xatom 1) 0 | 9 => SOff (xatom 2) 0
  | 18 => SOff (xatom 3) 0 | 19 => SOff (xatom 4) 0 | 20 => SOff (xatom 5) 0 | 21 => SOff (xatom 6) 0
  | 22 => SOff (xatom 7) 0 | 23 => SOff (xatom 8) 0 | 24 => SOff (xatom 9) 0 | 25 => SOff (xatom 10) 0
  | 26 => SOff (xatom 11) 0 | 27 => SOff (xatom 12) 0
  | 3 => SOff 3 0 | 4 => SOff 4 0
  | _ => SLit 0
  end.
Lemma ps_epi_expect_ok : forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ps_epi_end) r) (ps_epi_expect r)) CALLEE_SAVED
  = true.
Proof. vm_compute. reflexivity. Qed.

(* an extra atom by its xatom index: xatom k is entry S k of the env's extra list (atom 32 is the shadow base) *)
Lemma ps_ew_x : forall regs extra k, ew (Ereg regs extra) (xatom k) = nth (S k) extra (Z_to_bv 64 0).
Proof. intros regs extra k. unfold xatom. change (33 + k)%nat with (32 + S k)%nat. apply ew_Ereg_extra. Qed.

(* ---- raising a journal's window top: a journal over the window [sp0 - STK, sp0) is one over the larger window
   [sp0 - STK, ot) - so with STK' = STK + (ot - sp0) and top ot - once [sp0, ot) is present at the end. Every
   kept clause only gets weaker; the stack bound astk_ok moves with ot. put_string_spec's wpost states its journal
   at that raised top (FSH_Fn_FORM 3a: the out-object sits in [sp0, ot), in the caller's frame); the walk's own
   journal starts at sp0 (ps_seg0), and this lifts it. ---- *)
Lemma ps_aj_raise : forall STK sp0 ot FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  sp0 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, sp0 <= a < ot -> apresent (w_H W') mem' a) ->
  ajournal tfibsegs B (STK + (ot - sp0)) ot FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 ot FP ly S W mem md own ly' S' W' mem' md' k
  (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17)
  Hle Hal Htop Hpres.
pose proof J15 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
unfold ajournal.
do 8 (split; [assumption|]).
split; [intros a Ha Hout; apply J9; [exact Ha | lia]|].
do 4 (split; [assumption|]).
split; [intros a Ha; destruct (Z.lt_ge_cases a sp0) as [Hlt | Hge]; [apply J14; lia | apply Hpres; lia]|].
split; [unfold astk_ok; repeat split; lia|].
split; assumption.
Qed.

(* GENERALIZED (a Theorem Labs lane, 2026-10-29) in two ways the closing theorem needs: the journal's window top `jt` is its own
   parameter (put_string_spec's wpost raises it to ot, above the entry sp sp0 that s0 holds), and the
   user-poisoned heads at the epilogue `Uc` may differ from the entry's `U` (each put may grow the writer's buffer,
   which moves a head: uswap). fsw_flag_storeU and fsw_retU are already generic in both. *)
Lemma ps_epilogue : forall STK jt sp0 FP ly S W0 mem0 md0 lyc Sc U Uc (W : world tfibsegs) regs2 regs0 memc mdc k pos
  (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  (* the env: the shadow base, the thirteen saved entry words and the flag address (xatom 0 .. 13), then the
     frame's shadow address as atom 47 (the epilogue state bases the frame's shadow region there) *)
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ ps_xs regs0 (flag_addr lyc 0 pos)
                               ++ [Z_to_bv 64 (shadow_addr (frame_addr lyc 0 pos))]))
    (ps_epi_ss PS_CLOSE_RET)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 PS_CLOSE_RET) memc (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK jt FP ly S W0 (unpoison U mem0) md0 [(0, pos)] lyc Sc W (unpoison Uc memc) mdc k ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  In (0, pos) (frames Sc) ->
  YK11.getr regs2 8%bv = Z_to_bv 64 sp0 -> YK11.getr regs2 9%bv = Z_to_bv 64 (sp0 - 192 - (sp0 - 192) mod 32) ->
  YK11.getr regs2 24%bv = Z_to_bv 64 (frame_addr lyc 0 pos) ->
  jt - STK <= sp0 - 208 -> sp0 <= jt -> 0 <= sp0 - 208 -> sp0 < 2 ^ 64 -> sp0 mod 16 = 0 ->
  YK11.getr regs2 8%bv = YK11.getr regs0 2%bv -> YK11.getr regs2 3%bv = YK11.getr regs0 3%bv ->
  YK11.getr regs2 4%bv = YK11.getr regs0 4%bv ->
  v_jalr (YK11.getr regs0 1%bv) 0 = YK11.getr regs0 1%bv ->
  (* Q at the final state, knowing what the epilogue wrote: only the saved words at s0, the re-aligned frame, the
     fake frame, its shadow and its flag byte (the five regions of ps_epi_ss); every other byte is memc's *)
  (forall ms' md',
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 104 <= a < sp0) ->
        ~ (sp0 - 192 - (sp0 - 192) mod 32 <= a < sp0 - 192 - (sp0 - 192) mod 32 + 88) ->
        ~ (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64) ->
        ~ (shadow_addr (frame_addr lyc 0 pos) <= a < shadow_addr (frame_addr lyc 0 pos) + 8) ->
        a <> flag_addr lyc 0 pos ->
        ms_mem ms' (Z_to_bv 64 a) = memc (Z_to_bv 64 a)) ->
     (* and the walk's journal and ARU at the final state, the frame released: a post clause that AR re-derives
        (cstr_ok of a string in a live block or in the image, FSW_strkit / FSW_rd) reads them, not the memory *)
     (exists mdj, ajournal tfibsegs B STK jt FP ly S W0 (unpoison U mem0) md0 [] lyc (stack_free_state 0 pos Sc) W
                    (unpoison Uc (ms_mem ms')) mdj k /\
                  ARU tfibsegs B lyc (stack_free_state 0 pos Sc) Uc W (ms_mem ms') mdj) ->
     Q lyc (stack_free_state 0 pos Sc) W (ms_regs ms') (ms_mem ms') md') ->
  SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 PS_CLOSE_RET) memc (seg_rom tfibsegs)) mdc)
    (fpostU tfibsegs B STK jt FP regs0 ly S U W0 mem0 md0 k Uc Q).
Proof.
intros STK jt sp0 FP ly S W0 mem0 md0 lyc Sc U Uc W regs2 regs0 memc mdc k pos Q HS HJ HARU Hin E8 E9 E24
  Hwin Hjt Hsp0 Hsp64 Hal16 P8 P3 P4 Hjalr HQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B lyc Sc Uc W memc mdc HARU) as HAR.
destruct (al_frames _ _ LAWS lyc Sc W (unpoison Uc memc) mdc 0 pos HAR Hin) as (Hal32 & Hfapp & Hfp & Hshp).
destruct (al_flag _ _ LAWS lyc Sc W (unpoison Uc memc) mdc 0 pos HAR Hin) as (_ & _ & Hflapp & _).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
set (X := fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]) in *.
assert (FLb : 4096 <= FL /\ FL + 1 <= 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in Hflapp; lia).
assert (Fb : 4096 <= F /\ F + 64 <= alloc_ceiling)
  by (unfold in_app, kLowShadowBeg, ASAN_CEIL in Hfapp; rewrite Hfb in Hfapp; lia).
assert (Hsh : 0 <= shadow_addr F /\ shadow_addr F + 8 <= 2 ^ 47)
  by (unfold shadow_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia).
assert (Hsp1 : sp0 - 208 <= sp0 - 192 - (sp0 - 192) mod 32 <= sp0 - 192)
  by (clear -Hal16; Z.div_mod_to_equations; lia).
set (sp1 := sp0 - 192 - (sp0 - 192) mod 32) in *.
assert (U8 : bv_unsigned (ew (Ereg regs2 X) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs2 X 8 8%bv eq_refl), E8; apply wz; lia).
assert (U9 : bv_unsigned (ew (Ereg regs2 X) 9) = sp1)
  by (rewrite (ew_Ereg_nat regs2 X 9 9%bv eq_refl), E9; apply wz; lia).
assert (U24 : bv_unsigned (ew (Ereg regs2 X) 24) = F)
  by (rewrite (ew_Ereg_nat regs2 X 24 24%bv eq_refl), E24; apply wz; lia).
assert (U46 : bv_unsigned (ew (Ereg regs2 X) (xatom 13)) = FL)
  by (unfold X, xatom; change (33 + 13)%nat with (32 + 14)%nat; rewrite ew_Ereg_extra; cbn [nth fs_extraT ps_xs app];
      apply wz; lia).
assert (U47 : bv_unsigned (ew (Ereg regs2 X) 47) = shadow_addr F)
  by (unfold X; change 47%nat with (32 + 15)%nat; rewrite ew_Ereg_extra; cbn [nth fs_extraT ps_xs app];
      apply wz; lia).
apply (fsw_flag_storeU B HML HASF HFFL fsw_ps_tbl fsw_ps_tbl_ok W FUEL (Ereg regs2 X) (ps_epi_ss PS_CLOSE_RET)
  ps_epi_end (RS_stopped (SR_jalr (SOff (xatom 0) 0))) (mkst regs2 (Z_to_bv 64 PS_CLOSE_RET) memc (seg_rom tfibsegs))
  STK jt FP ly S W0 (unpoison U mem0) md0 [] lyc Sc Uc mdc k 0 pos _).
- exact HS.
- exact ps_epi_run_eq.
- exact I.
- exact HJ.
- exact HARU.
- lia.
- (* every byte the run writes: the stack window, the frame and its shadow (the frame arm), or the flag *)
  intros a (r & Hr & Ha). cbn [ss_mem ps_epi_ss] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  + left. left. left. rewrite U8 in Ha. lia.
  + left. left. left. rewrite U9 in Ha. lia.
  + left. left. right; right; right. exists 0, pos. split; [left; reflexivity|]. left.
    unfold in_zr; cbn [fst snd]. rewrite U24 in Ha. fold F. rewrite Hfb. lia.
  + left. left. right; right; right. exists 0, pos. split; [left; reflexivity|]. right.
    unfold in_zr; cbn [fst snd]. rewrite U47 in Ha. fold F. rewrite Hfb. change (64 / 8) with 8. lia.
  + right. rewrite U46 in Ha. lia.
- intros msr HSr. exact (ps_epi_flag0 (Ereg regs2 X) msr HSr FL U46).
- intros ms' mat' HS' HJ' HARU' HFE _ _.
  (* the return address: register ra holds the saved ra atom xatom 0 *)
  assert (R1 : YK11.getr (ms_regs ms') 1%bv = YK11.getr regs0 1%bv).
  { rewrite (fsw_reg_extra _ regs2 X ps_epi_end ms' 1%bv 1 HS' ltac:(vm_compute; reflexivity)). reflexivity. }
  apply (fsw_retU B fsw_ps_tbl fsw_ps_tbl_ok W (Ereg regs2 X) ps_epi_end ms'
    (with_vm_backing (m_vm_lazy mdc) mat' mdc) STK jt FP regs0 ly S U W0 mem0 md0 lyc (stack_free_state 0 pos Sc) Uc k Q
    HS' ltac:(vm_compute; reflexivity) ps_epi_ret_word).
  + rewrite R1. exact Hjalr.
  + exact HJ'.
  + exact HARU'.
  + (* the callee-saved registers: reloaded saved words, sp back at the entry sp, gp / tp untouched *)
    apply (fsw_preserved (w_H W) (Ereg regs2 X) ps_epi_end ms' regs0 ps_epi_expect HS' ps_epi_expect_ok).
    intros r Hr. cbv [CALLEE_SAVED In] in Hr.
    repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
    all: unfold ps_epi_expect.
    all: lazymatch goal with |- context [bv_unsigned ?rr] =>
           let v := eval vm_compute in (bv_unsigned rr) in change (bv_unsigned rr) with v end.
    all: cbv iota.
    all: try rewrite fsw_SOff0.
    all: try first [ rewrite (ew_Ereg_nat regs2 X 8 8%bv eq_refl); exact P8
            | rewrite (ew_Ereg_nat regs2 X 3 3%bv eq_refl); exact P3
            | rewrite (ew_Ereg_nat regs2 X 4 4%bv eq_refl); exact P4
            | rewrite ps_ew_x; reflexivity ].
  + intros mat. apply HQ.
    * intros a Ha H104 H88 H64 H8 HFL. apply HFE. rewrite (wz a Ha). intros (rr & Hinr & Hrr).
      cbn [ss_mem ps_epi_ss In] in Hinr.
      destruct Hinr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr.
      -- rewrite U8 in Hrr. lia.
      -- rewrite U9 in Hrr. lia.
      -- rewrite U24 in Hrr. fold F in H64. lia.
      -- rewrite U47 in Hrr. fold F in H8. lia.
      -- rewrite U46 in Hrr. fold FL in HFL. lia.
    * exists (with_vm_backing (m_vm_lazy mdc) mat' mdc). split; [exact HJ' | exact HARU'].
Qed.

End W.
(* end of a Theorem Labs lane stretch 1 *)
