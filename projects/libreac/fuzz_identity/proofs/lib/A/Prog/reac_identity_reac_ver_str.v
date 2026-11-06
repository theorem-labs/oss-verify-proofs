(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8n.v:1199-1201
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-202, 358-363, 390-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:207-209 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:707-710 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8k.v:388-389. *)
(* reac_identity_reac_ver_str (fuzz_identity.asan 0x84044, listing offset AF_reac_identity_reac_ver_str =
   0x3938) on the ASan build: reac_identity_reac_ver_str (ma, mi, pa, o, c) returns -1 when o is null or
   c < 20; else it writes "ma.mi" and pa with two digits at least (the plain model,
   lib/Prog/reac_identity_reac_ver_str_c.v: reac_ver_str_VER) and a NUL at o, and returns the length.

   Callers. LLVMFuzzerTestOneInput calls it three times: at 0x80a24 with o = 0, at 0x81094 with a buffer
   in the entry's own side-stack frame (frame + 224, 20 bytes) and at 0x8176c with a heap block it got from
   malloc. A byte in a frame of the caller cannot be composed through YCbq.v ajournal_sub (it needs every
   written byte in a heap block or a tmp block), so the contract is in cgif's caller-journal form
   (lib/YC20.v:311-365; the shapes tcj_kept, twr_ok and tdst_ok of IdentCJ.v): the premise is the caller's
   journal, the right to write [o, o + 20) is the caller's per-byte premise, the post extends the same
   journal and says what the call keeps.

   Stack, measured from the listing: its own 48-byte frame (0x84044 addi sp,sp,-48) and, below it, the
   stack write_uint needs (WRITE_UINT_STK) at each of its three calls (0x84090, 0x840c0, 0x840f8).
   It allocates no heap block and takes no side-stack frame, and write_uint counts no event, so
   EV_REAC_VER_STR = 0. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentCJ IdentProgSig
YC81 YC4b YC1g YC1h YC85 write_uint.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require write_uint_c reac_identity_reac_ver_str_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition A_reac_identity_reac_ver_str : Z := BASE + AF_reac_identity_reac_ver_str.
Definition REAC_VER_STR_STK : Z := 48 + WRITE_UINT_STK.
Definition EV_REAC_VER_STR : Z := 0.
(* The digit count of one field and the whole string's length (the plain model). *)
Definition rvs_n (v : Z) : Z := write_uint_c.write_uint_n v.
Definition rvs_LV (ma mi pa : Z) : Z := reac_identity_reac_ver_str_c.reac_ver_str_LV ma mi pa.
Definition rvs_bytes (ma mi pa : Z) : list Z :=
  map (fun b : byte => bv_unsigned b) (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa) ++ [0].
(* The two cases in which the call returns -1 and writes nothing. *)
Definition rvs_fails (o c : Z) : bool := (o =? 0) || (c <? 20).
(* ---- the model facts the walk needs (the plain lib/Prog/reac_identity_reac_ver_str.v) --------- *)
Lemma rvs_lsd_len : forall k x, (length (write_uint_c.write_uint_lsd k x) <= k)%nat.
Proof.
induction k as [|k IH]; intros x; cbn [write_uint_c.write_uint_lsd length]; [lia|].
destruct (x <? 10); cbn [length]; [lia|]. specialize (IH (x / 10)). lia.
Qed.
Lemma rvs_lsd_pos : forall k x, (1 <= length (write_uint_c.write_uint_lsd (S k) x))%nat.
Proof. intros k x. cbn [write_uint_c.write_uint_lsd length]. lia. Qed.
Lemma rvs_n_range : forall v, 1 <= rvs_n v <= 5.
Proof.
intros v. unfold rvs_n, write_uint_c.write_uint_n, write_uint_c.write_uint_D. rewrite length_rev.
pose proof (rvs_lsd_len 5 v). pose proof (rvs_lsd_pos 4 v). lia.
Qed.
Lemma rvs_D_lt10 : forall v, 0 <= v < 10 ->
write_uint_c.write_uint_D v = [write_uint_c.write_uint_dg v].
Proof.
intros v Hv. unfold write_uint_c.write_uint_D.
cbn [write_uint_c.write_uint_lsd]. rewrite (proj2 (Z.ltb_lt v 10) ltac:(lia)).
cbn [rev app]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma rvs_n_lt10 : forall v, 0 <= v < 10 -> rvs_n v = 1.
Proof. intros v Hv. unfold rvs_n, write_uint_c.write_uint_n. rewrite rvs_D_lt10 by lia. reflexivity. Qed.
Lemma rvs_n_ge10 : forall v, 10 <= v -> 2 <= rvs_n v.
Proof.
intros v Hv. unfold rvs_n, write_uint_c.write_uint_n, write_uint_c.write_uint_D. rewrite length_rev.
cbn [write_uint_c.write_uint_lsd]. rewrite (proj2 (Z.ltb_ge v 10) ltac:(lia)). cbn [length].
pose proof (rvs_lsd_pos 3 (v / 10)). lia.
Qed.
Lemma rvs_LV_eq : forall ma mi pa,
rvs_LV ma mi pa = rvs_n ma + 1 + rvs_n mi + (if pa <? 10 then 2 else rvs_n pa).
Proof.
intros ma mi pa. unfold rvs_LV, reac_identity_reac_ver_str_c.reac_ver_str_LV,
reac_identity_reac_ver_str_c.reac_ver_str_VER, reac_identity_reac_ver_str_c.reac_ver_str_DEC2,
rvs_n, write_uint_c.write_uint_n.
rewrite !length_app. cbn [length]. destruct (pa <? 10); cbn [length]; lia.
Qed.
Section h.
Variable B : asyms.
(* The buffer: 20 bytes of one heap block or of one side-stack frame of the caller's state. *)
Definition rvs_dst (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= q /\ q + n <= b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\
 frame_addr lyc cid pos <= q /\ q + n <= frame_addr lyc cid pos + fs_frame_bytes cid).
Definition treac_identity_reac_ver_str_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (ma mi pa o c : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_REAC_VER_STR) /\
aregs_preserved regs regs2 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ frames S2 = frames Sc /\
if rvs_fails o c
then getr regs2 10 = w64 (-1) /\
     tcj_kept B REAC_VER_STR_STK lyc Sc W memc W2 mem2 (spZ regs) (fun _ => False)
else getr regs2 10 = w64 (rvs_LV ma mi pa) /\
     garr8 SEGS (mrestrict (w_H W2) mem2) o (rvs_bytes ma mi pa) /\
     tcj_kept B REAC_VER_STR_STK lyc Sc W memc W2 mem2 (spZ regs)
       (fun a => o <= a < o + rvs_LV ma mi pa + 1).
Definition treac_identity_reac_ver_str_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (ma mi pa o c : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_VER_STR_STK -> spZ regs <= sp0 ->
getr regs 10 = w64 ma -> getr regs 11 = w64 mi -> getr regs 12 = w64 pa ->
getr regs 13 = w64 o -> getr regs 14 = w64 c ->
0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
(rvs_fails o c = false ->
 twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 20 /\
 rvs_dst lyc Sc o 20 /\
 range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 20) ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr SEGS W (cfg_at SEGS A_reac_identity_reac_ver_str regs memc mdc)
(treac_identity_reac_ver_str_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs ma mi pa o c).
(* The string, in the pieces the walk writes. *)
Lemma rvs_bytes_split : forall ma mi pa, 0 <= pa ->
  rvs_bytes ma mi pa = write_uint.wu_bytes ma ++ [46] ++ write_uint.wu_bytes mi ++
    ((if pa <? 10 then [48] else []) ++ write_uint.wu_bytes pa) ++ [0].
Proof.
intros ma mi pa Hpa. unfold rvs_bytes, write_uint.wu_bytes, reac_identity_reac_ver_str_c.reac_ver_str_VER,
  reac_identity_reac_ver_str_c.reac_ver_str_DEC2.
rewrite !map_app, <- !app_assoc. destruct (Z.ltb_spec pa 10) as [Hl|Hl].
- rewrite (rvs_D_lt10 pa) by lia. reflexivity.
- reflexivity.
Qed.
Lemma rvs_wu_len : forall v, Z.of_nat (length (write_uint.wu_bytes v)) = rvs_n v.
Proof. intros v. unfold write_uint.wu_bytes. rewrite length_map. reflexivity. Qed.
(* ---- the walk's symbolic start state -------------------------------------------------------------
   Atoms 0..31 are the registers at entry (a0 = ma is atom 10, a1 = mi 11, a2 = pa 12, a3 = o 13, a4 = c 14);
   atom 32 is the shadow offset the shadow cell holds; atoms 33..40 are values the arguments fix: the three
   digit counts n1, n2, n3 (33, 34, 35), o + n1 (36), n1 + n2 (37), o + n1 + n2 (38), n1 + n2 + n3 (39) and
   o + n1 + n2 + n3 (40). After each write_uint call the walk sets a0 to atom 33, 34 or 35 (the callee's
   post-condition gives its value). The aliases let the walk see each address the body computes -- o plus a
   32-bit sum of digit counts -- as an offset of atom 36, 38 or 40, which is what the regions and the shadow
   entries are stated over. The regions: the 48-byte frame below sp, the GOT slot of the shadow cell, the
   shadow cell, and the bytes of the buffer the call writes itself: '.' at o + n1, the padding '0' at
   o + n1 + n2 + 1 (written when pa < 10; the third write_uint call writes that byte otherwise) and the NUL
   at o + n1 + n2 + n3 + kN (kN = 2 when pa < 10, 1 otherwise). *)
Definition rvs_SB : Z := 0x7fff8000.
Definition rvs_Bx : sv := SOff 32 0.
Definition rvs_Bspan : Z * Z := (rvs_SB, rvs_SB + 2 ^ 44 - 1).
Definition rvs_OH : Z := 2 ^ 47 - 20.
Definition rvs_rD : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 1 [].
Definition rvs_rP : YP09.region := YP09.mkRegion (Some 38%nat) 1 2 1 2 [].
Definition rvs_rN (kN : Z) : YP09.region := YP09.mkRegion (Some 40%nat) kN (kN + 1) kN (kN + 1) [].
Definition rvs_rs (kN : Z) : YP09.smem :=
  [stack_region 48; got_regionP; bcell_regionP 32; rvs_rD; rvs_rP; rvs_rN kN].
Definition rvs_GA (lo12 hi12 : Z) : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 65535 0); (11%nat, mkAF 0 65535 0);
    (12%nat, mkAF lo12 hi12 0); (13%nat, mkAF 4096 rvs_OH 0); (14%nat, mkAF 20 (2 ^ 64 - 1) 0);
    (32%nat, mkAF rvs_SB rvs_SB 0); (33%nat, mkAF 1 5 0); (34%nat, mkAF 1 5 0); (35%nat, mkAF 1 5 0);
    (36%nat, mkAF 4097 (rvs_OH + 5) 0); (37%nat, mkAF 2 10 0); (38%nat, mkAF 4098 (rvs_OH + 10) 0);
    (39%nat, mkAF 3 15 0); (40%nat, mkAF 4099 (rvs_OH + 15) 0) ].
Definition rvs_XC (p : nat) (d : Z) : acond :=
  mkAC BC_NE (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff p d) (SOff 13 0)) (SLit 0)) (SLit 1)) (SLit 0).
Definition rvs_GC : list acond := [rvs_XC 36 0; rvs_XC 36 1; rvs_XC 38 1; rvs_XC 38 2; rvs_XC 40 1; rvs_XC 40 2].
(* The 32-bit sums the body builds: s4 = n1 + 1, s2 = n2 + s4 and, when pa < 10, s2 + 1; after the third
   call a0 = n3 + s2. Each address is o plus one of them. *)
Definition rvs_w1 : sv := SAluw ALU_ADD (SOff 33 0) (SLit 1).
Definition rvs_w2 : sv := SAluw ALU_ADD (SOff 34 0) rvs_w1.
Definition rvs_w2p : sv := SAluw ALU_ADD rvs_w2 (SLit 1).
Definition rvs_s2 (d : Z) : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 d) (SOff 33 0)) (SOff 34 0).
Definition rvs_s3 (d : Z) : sv := SAlu ALU_ADD (rvs_s2 d) (SOff 35 0).
Definition rvs_GL : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 13 0) (SOff 33 0), SOff 36 0);
    (SAlu ALU_ADD (SOff 13 0) rvs_w1, SOff 36 1);
    (SAlu ALU_ADD (SOff 13 0) rvs_w2, SOff 38 1);
    (SAlu ALU_ADD (SOff 13 0) rvs_w2p, SOff 38 2);
    (SAlu ALU_ADD (SOff 13 0) (SAluw ALU_ADD (SOff 35 0) rvs_w2), SOff 40 1);
    (SAlu ALU_ADD (SOff 13 0) (SAluw ALU_ADD (SOff 35 0) rvs_w2p), SOff 40 2);
    (rvs_s2 1, SOff 38 1); (rvs_s2 2, SOff 38 2);
    (rvs_s3 1, SOff 40 1); (rvs_s3 2, SOff 40 2) ].
Definition rvs_SH (kN : Z) : list shent := [mkSHE 36 0 1; mkSHE 38 1 2; mkSHE 40 kN (kN + 1)].
Definition rvs_ss (kN lo12 hi12 : Z) : sstate :=
  mkSS AF_reac_identity_reac_ver_str sr_atoms (rvs_rs kN) None (mkFacts (rvs_GA lo12 hi12) rvs_GC rvs_GL).
Definition rvs_extra (ma mi pa o : Z) : list word :=
  map (Z_to_bv 64) [rvs_SB; rvs_n ma; rvs_n mi; rvs_n pa; o + rvs_n ma; rvs_n ma + rvs_n mi;
    o + rvs_n ma + rvs_n mi; rvs_n ma + rvs_n mi + rvs_n pa; o + rvs_n ma + rvs_n mi + rvs_n pa].
Definition rvs_E (regs : bvmap 5 word) (ma mi pa o : Z) : env := Eimg (Ereg regs (rvs_extra ma mi pa o)).
(* The start state of the two paths that return -1: the frame only. *)
Definition rvs_ssF (lo13 hi13 lo14 hi14 : Z) : sstate :=
  mkSS AF_reac_identity_reac_ver_str sr_atoms [stack_region 48] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (13%nat, mkAF lo13 hi13 0); (14%nat, mkAF lo14 hi14 0)] [] []).
(* No pointer sum wraps: the conditions of rvs_GC hold. *)
Lemma rvs_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z H. unfold zcanon, M64. apply Z.mod_small. exact H. Qed.
(* Innermost-first removal of zcanon from a nested sum of small values. *)
Ltac rvs_zcs :=
  repeat match goal with
  | |- context [zcanon ?z] =>
      tryif (match z with context [zcanon _] => idtac end) then fail else rewrite (rvs_zc z) by lia
  end.
Lemma rvs_XC_ok : forall E (p : nat) d,
  bv_unsigned (ew E 13) <= bv_unsigned (ew E p) + d < 2 ^ 64 -> acond_ok E (rvs_XC p d).
Proof.
intros E p d H. unfold acond_ok, rvs_XC. cbn [ac_c ac_a ac_b branch_taken].
pose proof (bv_unsigned_in_range 64 (ew E 13)) as R13. change (bv_modulus 64) with (2 ^ 64) in R13.
assert (HU : U E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff p d) (SOff 13 0)) (SLit 0)) (SLit 1)) = 1).
{ rewrite !U_SAlu, !U_SLit, !U_SOff. cbn [zalu_raw].
  rewrite (rvs_zc (bv_unsigned (ew E p) + d)) by lia. rewrite (rvs_zc (bv_unsigned (ew E 13) + 0)) by lia.
  destruct (Z.ltb_spec (bv_unsigned (ew E p) + d) (bv_unsigned (ew E 13) + 0)) as [X|X]; [lia|]. reflexivity. }
unfold U in HU. rewrite bv_eqb_unsigned, HU. reflexivity.
Qed.
(* A byte the walk stored, read back from its region's one-byte chunk. *)
Lemma rvs_U_addw : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 31 ->
  U E (SAluw ALU_ADD a b) = x + y.
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite Ha, Hb.
rewrite !(Z.mod_small) by lia. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (x + y + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rvs_le_byte1 : forall b : byte, Z_to_bv 8 (le_byte (bv_unsigned b) 1 0) = b.
Proof.
intros b. unfold le_byte. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma rvs_garr8_chunk : forall E m base off (e : sv) v,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 e)) ->
  bv_unsigned (byte_of_word (sv_denot E e) 0) = v -> garr8 SEGS m (base + off) [v].
Proof.
intros E m base off e v Hc He j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth].
pose proof (bv_unsigned_in_range 8 (byte_of_word (sv_denot E e) 0)) as Hr. change (bv_modulus 8) with 256 in Hr.
destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. injection Hb1 as Hb1. subst b.
rewrite <- He. split; [|lia].
intros kk Hk. assert (kk = 0%nat) by lia. subst kk.
replace (base + off + Z.of_nat 0 + Z.of_nat 0) with (base + off + 0) by lia. rewrite Hb2. f_equal.
symmetry. apply rvs_le_byte1.
Qed.
Lemma rvs_byte_reg : forall E m (n : nat) lo hi wlo whi off (e : sv) v base,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi [YP09.mkChunk off (CVal 1 e)]) ->
  base_val E (Some n) = base -> bv_unsigned (byte_of_word (sv_denot E e) 0) = v -> garr8 SEGS m (base + off) [v].
Proof.
intros E m n lo hi wlo whi off e v base (_ & _ & _ & HCH) Hb He.
cbn [YP09.r_chunks YP09.r_base] in HCH. rewrite Hb in HCH. apply Forall_inv in HCH.
exact (rvs_garr8_chunk E m base off e v HCH He).
Qed.
Lemma rvs_fs_mod8 : forall c, 20 <= fs_frame_bytes c -> fs_frame_bytes c mod 8 = 0.
Proof.
intros c H. unfold fs_frame_bytes in *. destruct (Z_le_gt_dec 0 c) as [Hc|Hc].
- rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z.mod_mul. lia.
- rewrite Z.shiftl_div_pow2 in H by lia. rewrite Z.shiftl_div_pow2 by lia.
  assert (Hc3 : c = -1 \/ c = -2 \/ c <= -3) by lia.
  destruct Hc3 as [-> | [-> | Hc3]]; [reflexivity | reflexivity |].
  exfalso. assert (Hp : 8 <= 2 ^ (- c)) by (change 8 with (2 ^ 3); apply Z.pow_le_mono_r; lia).
  assert (Hd : 64 / 2 ^ (- c) <= 64 / 8) by (apply Z.div_le_compat_l; lia). change (64 / 8) with 8 in Hd. lia.
Qed.
Lemma rvs_aview_frame : forall (W : world SEGS) m1 m2 (P : Z -> Prop) a, 0 <= a < 2 ^ 64 -> P a ->
  (forall x : word, P (bv_unsigned x) -> mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x) ->
  aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof. intros W m1 m2 P a Ha HP HK. unfold aview, mbyte. rewrite HK; [reflexivity|]. rewrite unsigned_lit_small by lia. exact HP. Qed.
Lemma rvs_ra_shadow : forall (W1 W2 : world SEGS) m1 m2 q n,
  range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF q n ->
  (forall x, q <= x < q + n -> aview SEGS (w_H W2) m2 (shadow_addr x) = aview SEGS (w_H W1) m1 (shadow_addr x)) ->
  range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF q n.
Proof.
intros W1 W2 m1 m2 q n HR HK x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
specialize (HK x Hx). unfold shadow_of_addr in *. unfold shadow_addr in HK. rewrite HK. exact Hs.
Qed.
Lemma rvs_garr8_1 : forall m a v, val_mem SEGS m a 1 v -> 0 <= v < 256 -> garr8 SEGS m a [v].
Proof.
intros m a v H Hv j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth].
rewrite Z.add_0_r. split; [exact H | exact Hv].
Qed.
(* ---- what a piece of the call keeps: IdentBCJ.tcj_kept without its last clause ----------------- *)
Definition rvs_k (lyc : alayout) (Sc : astate) (W1 : world SEGS) (m1 : word -> option byte)
(W2 : world SEGS) (m2 : word -> option byte) (lo hi : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ E a ->
 aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
 aview SEGS (w_H W2) m2 (b + i) = aview SEGS (w_H W1) m1 (b + i)) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
 (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
 ~ E a -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
 apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a).
Lemma rvs_k_trans : forall lyc Sc W1 m1 W2 m2 W3 m3 lo hi E1 E2,
rvs_k lyc Sc W1 m1 W2 m2 lo hi E1 -> rvs_k lyc Sc W2 m2 W3 m3 lo hi E2 ->
rvs_k lyc Sc W1 m1 W3 m3 lo hi (fun a => E1 a \/ E2 a).
Proof.
intros lyc Sc W1 m1 W2 m2 W3 m3 lo hi E1 E2 (A1 & A2 & A3 & A4 & A5) (C1 & C2 & C3 & C4 & C5).
split; [intros a Ha Hw He; rewrite (C1 a Ha Hw ltac:(tauto)); exact (A1 a Ha Hw ltac:(tauto))|].
split; [intros b m i Hin Hi He; rewrite (C2 b m i Hin Hi ltac:(tauto)); exact (A2 b m i Hin Hi ltac:(tauto))|].
split; [intros a Hi Hs He; rewrite (C3 a Hi Hs He); exact (A3 a Hi Hs He)|].
split; [intros cid pos a Hin Hr He; rewrite (C4 cid pos a Hin Hr ltac:(tauto)); exact (A4 cid pos a Hin Hr ltac:(tauto))|].
intros a Ha Hw Hp. exact (C5 a Ha Hw (A5 a Ha Hw Hp)).
Qed.
Lemma rvs_k_mono : forall lyc Sc W1 m1 W2 m2 lo hi lo' hi' (E E' : Z -> Prop),
rvs_k lyc Sc W1 m1 W2 m2 lo hi E -> lo' <= lo -> hi <= hi' -> (forall a, E a -> E' a) ->
rvs_k lyc Sc W1 m1 W2 m2 lo' hi' E'.
Proof.
intros lyc Sc W1 m1 W2 m2 lo hi lo' hi' E E' (A1 & A2 & A3 & A4 & A5) Hlo Hhi HE.
split; [intros a Ha Hw He; apply A1; [exact Ha | lia | intros X; exact (He (HE a X))]|].
split; [intros b mm i Hin Hi He; apply (A2 b mm i); [exact Hin | exact Hi | intros X; exact (He (HE (b + i) X))]|].
split; [exact A3|].
split; [intros cid pos a Hin Hr He; apply (A4 cid pos a); [exact Hin | exact Hr | intros X; exact (He (HE a X))]|].
intros a Ha Hw Hp. apply A5; [exact Ha | lia | exact Hp].
Qed.
Lemma rvs_k_of_tcj : forall STK lyc Sc W1 m1 W2 m2 sp E,
tcj_kept B STK lyc Sc W1 m1 W2 m2 sp E -> rvs_k lyc Sc W1 m1 W2 m2 (sp - STK) sp E.
Proof.
intros STK lyc Sc W1 m1 W2 m2 sp E (A1 & A2 & A3 & A4 & A5 & _).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4 | exact A5].
Qed.
(* The journal adds the clause tcj_kept asks for: the whole stack window is there at the end. *)
Lemma rvs_tcj_of_k : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 lyc Sc W1 m1 W2 m2 md2 k sp (E : Z -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m2 md2 k ->
rvs_k lyc Sc W1 m1 W2 m2 (sp - REAC_VER_STR_STK) sp E ->
sp0 - STK <= sp - REAC_VER_STR_STK -> sp <= sp0 ->
tcj_kept B REAC_VER_STR_STK lyc Sc W1 m1 W2 m2 sp E.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 lyc Sc W1 m1 W2 m2 md2 k sp E HJ (A1 & A2 & A3 & A4 & A5) Hlo Hhi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
intros a Ha. apply Hpres. lia.
Qed.
(* A piece stated for a later state with the same blocks and frames is one for the entry state. *)
Lemma rvs_k_move : forall ly1 S1 ly2 S2 W1 m1 W2 m2 lo hi E,
rvs_k ly2 S2 W1 m1 W2 m2 lo hi E ->
Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) -> frames S2 = frames S1 ->
(forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos) ->
rvs_k ly1 S1 W1 m1 W2 m2 lo hi E.
Proof.
intros ly1 S1 ly2 S2 W1 m1 W2 m2 lo hi E (A1 & A2 & A3 & A4 & A5) Hp Hf Hfa.
split; [exact A1|].
split; [intros b m i Hin Hi He; exact (A2 b m i (Permutation_in _ (Permutation_sym Hp) Hin) Hi He)|].
split; [exact A3|].
split; [|exact A5].
intros cid pos a Hin Hr He. apply (A4 cid pos a); [rewrite Hf; exact Hin | | exact He].
unfold frame_rng in *. cbn [fst snd] in *. rewrite !Hfa. exact Hr.
Qed.
Lemma rvs_journal_move : forall STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 md2 k2,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k1 ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m2 md2 k2 ->
frames S2 = frames S1 /\ (forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 md2 k2
  (_ & Hly1 & _ & _ & _ & Hf1 & _) (_ & Hly2 & _ & _ & _ & Hf2 & _).
split; [rewrite Hf1, Hf2; reflexivity|].
intros cid pos. unfold frame_addr. destruct Hly1 as (_ & _ & _ & _ & _ & E1 & _). destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _).
rewrite E1, E2. reflexivity.
Qed.
Lemma rvs_dst_move : forall ly1 S1 ly2 S2 q n, rvs_dst ly1 S1 q n ->
Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) -> frames S2 = frames S1 ->
(forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos) -> rvs_dst ly2 S2 q n.
Proof.
intros ly1 S1 ly2 S2 q n [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] Hp Hf Hfa.
- left. exists b, m. split; [exact (Permutation_in _ (Permutation_sym Hp) Hin) | lia].
- right. exists cid, pos. rewrite Hf, Hfa. split; [exact Hin | lia].
Qed.
Lemma rvs_awr_move : forall STK sp0 FP bl0 ly1 S1 ly2 S2 own a,
awr_byte STK sp0 FP bl0 (ablocks B ly1 S1) ly1 own a ->
Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) ->
(forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos) ->
awr_byte STK sp0 FP bl0 (ablocks B ly2 S2) ly2 own a.
Proof.
intros STK sp0 FP bl0 ly1 S1 ly2 S2 own a [Hw | [(Hfp & b & n & Hin & Hb) | [(b & n & Hin & Hn0 & Hb) | (cid & pos & Hin & Hr)]]] Hp Hfa.
- left. exact Hw.
- right. left. split; [exact Hfp|]. exists b, n. split; [exact (Permutation_in _ (Permutation_sym Hp) Hin) | exact Hb].
- right. right. left. exists b, n. split; [exact (Permutation_in _ (Permutation_sym Hp) Hin) | split; [exact Hn0 | exact Hb]].
- right. right. right. exists cid, pos. rewrite !Hfa. split; [exact Hin | exact Hr].
Qed.
Lemma rvs_k_byte : forall lyc Sc W1 m1 W2 m2 lo hi (E : Z -> Prop) q n a,
rvs_k lyc Sc W1 m1 W2 m2 lo hi E -> rvs_dst lyc Sc q n -> q <= a < q + n -> ~ E a ->
aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a.
Proof.
intros lyc Sc W1 m1 W2 m2 lo hi E q n a (_ & A2 & _ & A4 & _) [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] Ha He.
- replace a with (b + (a - b)) by lia. apply (A2 b m (a - b) Hin); [lia | replace (b + (a - b)) with a by lia; exact He].
- apply (A4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact He].
Qed.
Lemma rvs_dst_tdst : forall lyc Sc o n, rvs_dst lyc Sc o n -> tdst_ok B lyc Sc o n.
Proof.
intros lyc Sc o n [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] a Ha.
- left. exists b, m. split; [exact Hin | lia].
- right. exists cid, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.
Lemma rvs_dst_sub : forall lyc Sc o n q m, rvs_dst lyc Sc o n -> o <= q -> q + m <= o + n -> rvs_dst lyc Sc q m.
Proof.
intros lyc Sc o n q m [(b & mm & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] Hq Hm.
- left. exists b, mm. split; [exact Hin | lia].
- right. exists cid, pos. split; [exact Hin | lia].
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : ident_prog_sig_ok.
Hypothesis TWU : write_uint.twrite_uint_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).
(* Where the buffer lies: app memory below the allocation ceiling, present, the client's, not the image. *)
Lemma rvs_dst_facts : forall ly S W mem md q n, AR SEGS B ly S W mem md -> rvs_dst ly S q n -> 0 < n ->
4096 <= q /\ q + n <= alloc_ceiling /\ in_app q n /\
(forall a, q <= a < q + n -> apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ in_img SEGS a).
Proof.
intros ly S W mem md q n HAR [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] Hn.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hcl & Happ & Hb & _).
  split; [lia|]. split; [lia|]. split; [eapply in_app_sub; [exact Happ | lia | lia | lia]|].
  intros a Ha. destruct (Hb a ltac:(lia)) as [Hp Ho]. split; [exact Hp|]. split; [exact Ho|].
  assert (Hab : b <= a < b + req_size m) by lia.
  exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Hab)))))).
- destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (_ & Happ & Hb & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (H4096 & Hcl & _).
  split; [lia|]. split; [lia|]. split; [eapply in_app_sub; [exact Happ | lia | lia | lia]|].
  intros a Ha. destruct (Hb a ltac:(lia)) as [Hp Ho]. split; [exact Hp|]. split; [exact Ho|].
  assert (Hab : frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) by lia.
  exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR
    (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Hab))))))).
Qed.
(* A run that changed no byte outside [lo, hi) (at or above the allocation ceiling) and the bytes E (none of
   them in the image), and lost no byte, kept what rvs_k says; the entry AR fixes the blocks and frames. *)
Lemma rvs_k_of_run : forall lyc Sc W memc mdc m1 m2 lo hi (E : Z -> Prop),
AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
(forall a, in_img SEGS a -> ~ E a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ E a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
rvs_k lyc Sc W m1 W m2 lo hi E.
Proof.
intros lyc Sc W memc mdc m1 m2 lo hi E HAR Hlo Hhi HimgE KV HG.
assert (KP : forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a).
{ intros a (Hh & b & Hb). split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG.
  rewrite Hh, Hb in HG. destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity]. }
pose proof asan_consts as (C1 & _).
split; [intros a Ha Hw He; apply KV; [lia | exact Hw | exact He]|].
split.
{ intros b m i Hin Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hcl & _).
  apply KV; [lia | lia | exact He]. }
split.
{ intros a Hi Hns Herr. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  apply KV; [lia | lia | exact (HimgE a Hi)]. }
split.
{ intros cid pos a Hin Hr He.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf0 & _ & _).
  destruct (frame_zone SEGS B LAWS _ _ _ _ _ cid pos a HAR Hin Hr) as (Hza & [(Hz1 & _) | Hz2]);
  (apply KV; [unfold kLowMemEnd in *; lia | lia | exact He]). }
intros a Ha Hw Hp. exact (KP a Hp).
Qed.
(* The buffer's shadow after a write_uint call: a heap block's from the allocator invariant, a frame's because
   the call kept its caller's frames' shadow. *)
Lemma rvs_ra_call : forall STK' lyk Sk ly2 S2 W mk m2 mdk md2 sp (E : Z -> Prop) q n,
AR SEGS B lyk Sk W mk mdk -> AR SEGS B ly2 S2 W m2 md2 ->
Permutation (ablocks B ly2 S2) (ablocks B lyk Sk) ->
rvs_dst lyk Sk q n -> 20 <= n -> in_app q n ->
range_addressable (aview SEGS (w_H W) mk) SHADOW_OFF q n ->
tcj_kept B STK' lyk Sk W mk W m2 sp E -> (forall a, E a -> q <= a < q + n) ->
range_addressable (aview SEGS (w_H W) m2) SHADOW_OFF q n.
Proof.
intros STK' lyk Sk ly2 S2 W mk m2 mdk md2 sp E q n HARk HAR2 Hperm HDk Hn Happ HR (_ & _ & _ & A4 & _) HE.
destruct HDk as [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)].
- exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ b m q n HAR2 (Permutation_in _ (Permutation_sym Hperm) Hin) H1 H2).
- destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HARk Hin) as (Hal & _).
  pose proof (rvs_fs_mod8 cid ltac:(lia)) as Hf8. apply mod32_mod8 in Hal.
  apply (rvs_ra_shadow W W mk m2 q n HR). intros x Hx. apply (A4 cid pos (shadow_addr x) Hin).
  + right. unfold in_zr, shadow_addr. cbn [fst snd].
    pose proof (Z.div_mod (frame_addr lyk cid pos) 8 ltac:(lia)) as D1.
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
    pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
    rewrite Hal in D1. rewrite Hf8 in D2. lia.
  + intros Hex. pose proof (HE _ Hex) as Hq. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    unfold in_app, ASAN_CEIL in Happ.
    pose proof (YCbq.shadow_addr_bounds x ltac:(unfold kHighMemEnd, kLowShadowBeg, kHighMemBeg in *; lia)) as Hsb.
    unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *. lia.
Qed.
(* Set register r to atom n when the machine's register holds that atom's value. *)
Lemma rvs_pin : forall E ss ms (r : bv 5) (n : nat),
st_ok_pi SEGS VAL E ss ms -> getr (ms_regs ms) r = sv_denot E (SOff n 0) -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r n HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r (SOff n 0)) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
  rewrite <- Hq, Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
(* ---- the start states hold ------------------------------------------------------------------- *)
Lemma rvs_entry_w : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  ma mi pa o c kN lo12 hi12,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= spZ regs - REAC_VER_STR_STK -> spZ regs <= sp0 -> spZ regs mod 16 = 0 ->
getr regs 10 = w64 ma -> getr regs 11 = w64 mi -> getr regs 12 = w64 pa -> getr regs 13 = w64 o ->
getr regs 14 = w64 c ->
0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= lo12 -> lo12 <= pa <= hi12 -> hi12 < 65536 -> 20 <= c < 2 ^ 64 ->
(kN = 1 \/ kN = 2) -> rvs_dst lyc Sc o 20 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 20 ->
st_ok_pi SEGS VAL (rvs_E regs ma mi pa o) (rvs_ss kN lo12 hi12)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_identity_reac_ver_str) memc (seg_rom SEGS))) /\
sh_ok SEGS rvs_Bx (rvs_SH kN) (rvs_E regs ma mi pa o) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c kN lo12 hi12
  HJ Hlo Hhi Hal16 H10 H11 H12 H13 H14 Rma Rmi Rlo12 Rpa Rhi12 Rc HkN HD HRA.
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_VER_STR_STK = 4224) by reflexivity.
destruct (rvs_dst_facts lyc Sc W memc mdc o 20 HAR HD ltac:(lia)) as (Ho4096 & HoC & Happ & HBY).
assert (Hoff : o + 20 <= IMG_LO \/ IMG_TOP <= o).
{ destruct HD as [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)];
  [ pose proof (blk_off_imgP B _ _ _ _ _ b m HAR Hin) as X | pose proof (frm_off_imgP B _ _ _ _ _ cid pos HAR Hin) as X ]; lia. }
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1%nat ltac:(lia)) as HgotR. pose proof (pa_obj_img 30%nat ltac:(lia)) as HcellR.
pose proof (pa_val_range (A_OBJ 1)) as HgotV. pose proof (pa_val_range (A_OBJ 30)) as HcellV.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (rvs_n_range ma) as N1. pose proof (rvs_n_range mi) as N2. pose proof (rvs_n_range pa) as N3.
set (E := rvs_E regs ma mi pa o).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rvs_extra ma mi pa o)) n)
  by (intros n Hn; subst E; unfold rvs_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ma) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 mi) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 pa) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 rvs_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rvs_n ma)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (rvs_n mi)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (rvs_n pa)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (o + rvs_n ma)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (rvs_n ma + rvs_n mi)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (o + rvs_n ma + rvs_n mi)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (rvs_n ma + rvs_n mi + rvs_n pa)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (o + rvs_n ma + rvs_n mi + rvs_n pa)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (Eg : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold rvs_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ec : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; unfold rvs_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
assert (UA : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v)
  by (intros n v Hn Hv; rewrite Hn; apply unsigned_lit_small; exact Hv).
assert (UO : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v)
  by (intros n v Hn Hv; rewrite U_SOff, Hn, unsigned_lit_small, Z.add_0_r by exact Hv; apply rvs_zc; exact Hv).
split.
- rewrite restrict_mkst_fx. unfold rvs_ss, A_reac_identity_reac_ver_str. apply pa_entry_st_ok_full.
  + subst E. unfold rvs_E. apply regs_ok_Eimg_Ereg.
  + destruct HkN as [-> | ->]; vm_compute; reflexivity.
  + unfold rvs_rs, stack_region, got_regionP, bcell_regionP, rvs_rD, rvs_rP, rvs_rN.
    repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia.
      split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
      [cbn [sv_denot]; rewrite Ec, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Ec) by lia.
      split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 rvs_Bx rvs_SB);
      [cbn [sv_denot rvs_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold rvs_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB 36%nat _ E36) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply (proj1 (HBY (o + rvs_n ma + q) ltac:(lia))).
    * rewrite (VB 38%nat _ E38) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply (proj1 (HBY (o + rvs_n ma + rvs_n mi + q) ltac:(lia))).
    * rewrite (VB 40%nat _ E40) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS).
      apply (proj1 (HBY (o + rvs_n ma + rvs_n mi + rvs_n pa + q) ltac:(destruct HkN; lia))).
  + apply pairwise_disjoint_of_extents.
    unfold rvs_rs, stack_region, got_regionP, bcell_regionP, rvs_rD, rvs_rP, rvs_rN, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Ec) by lia.
    rewrite (VB 36%nat _ E36) by lia. rewrite (VB 38%nat _ E38) by lia. rewrite (VB 40%nat _ E40) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 WS Hlo Hhi HgotR HcellR HgcD Ho4096 HoC Hoff N1 N2 N3 HkN. clear.
    intros. repeat split; lia.
  + split; [|split].
    * cbn [rvs_GA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, (UA 10%nat ma E10), (UA 11%nat mi E11), (UA 12%nat pa E12), (UA 13%nat o E13), (UA 14%nat c E14),
        (UA 32%nat _ E32), (UA 33%nat _ E33), (UA 34%nat _ E34), (UA 35%nat _ E35), (UA 36%nat _ E36),
        (UA 37%nat _ E37), (UA 38%nat _ E38), (UA 39%nat _ E39), (UA 40%nat _ E40) by (unfold rvs_SB; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1 WS Hal16 Hlo Hhi Rma Rmi Rlo12 Rpa Rhi12 Rc Ho4096 HoC N1 N2 N3. clear.
      unfold rvs_SB, rvs_OH. intros. repeat match goal with |- _ /\ _ => split end; lia.
    * cbn [rvs_GC f_conds conds_ok].
      repeat match goal with |- _ /\ _ => split end; try exact I; apply rvs_XC_ok;
      rewrite (UA 13%nat o E13) by lia;
      first [ rewrite (UA 36%nat _ E36) by lia | rewrite (UA 38%nat _ E38) by lia | rewrite (UA 40%nat _ E40) by lia ]; lia.
    * assert (UW1 : U E rvs_w1 = rvs_n ma + 1)
        by (unfold rvs_w1; apply (rvs_U_addw E _ _ (rvs_n ma) 1);
            [exact (UO 33%nat _ E33 ltac:(lia)) | apply U_lit; lia | lia | lia | lia]).
      assert (UW2 : U E rvs_w2 = rvs_n mi + (rvs_n ma + 1))
        by (unfold rvs_w2; apply (rvs_U_addw E _ _ (rvs_n mi) (rvs_n ma + 1));
            [exact (UO 34%nat _ E34 ltac:(lia)) | exact UW1 | lia | lia | lia]).
      assert (UW2p : U E rvs_w2p = rvs_n mi + (rvs_n ma + 1) + 1)
        by (unfold rvs_w2p; apply (rvs_U_addw E _ _ (rvs_n mi + (rvs_n ma + 1)) 1);
            [exact UW2 | apply U_lit; lia | lia | lia | lia]).
      assert (UW3 : U E (SAluw ALU_ADD (SOff 35 0) rvs_w2) = rvs_n pa + (rvs_n mi + (rvs_n ma + 1)))
        by (apply (rvs_U_addw E _ _ (rvs_n pa) (rvs_n mi + (rvs_n ma + 1)));
            [exact (UO 35%nat _ E35 ltac:(lia)) | exact UW2 | lia | lia | lia]).
      assert (UW3p : U E (SAluw ALU_ADD (SOff 35 0) rvs_w2p) = rvs_n pa + (rvs_n mi + (rvs_n ma + 1) + 1))
        by (apply (rvs_U_addw E _ _ (rvs_n pa) (rvs_n mi + (rvs_n ma + 1) + 1));
            [exact (UO 35%nat _ E35 ltac:(lia)) | exact UW2p | lia | lia | lia]).
      cbn [rvs_GL f_alias alias_ok].
      repeat match goal with |- _ /\ _ => split end; try exact I;
      apply U_inj; try unfold rvs_s3; try unfold rvs_s2; rewrite ?U_SAlu; cbn [zalu_raw];
               rewrite ?UW1, ?UW2, ?UW2p, ?UW3, ?UW3p by lia;
               rewrite ?(UO 13%nat o E13), ?(UO 33%nat _ E33), ?(UO 34%nat _ E34), ?(UO 35%nat _ E35) by lia;
               rewrite ?U_SOff;
               rewrite ?(UA 13%nat o E13), ?(UA 33%nat _ E33), ?(UA 34%nat _ E34), ?(UA 35%nat _ E35),
                 ?(UA 36%nat _ E36), ?(UA 38%nat _ E38), ?(UA 40%nat _ E40) by lia;
               rvs_zcs; lia.
- unfold sh_ok, rvs_SH. pose proof (UO 32%nat rvs_SB E32 ltac:(unfold rvs_SB; lia)) as UB.
  repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart, rvs_Bx; cbn [she_m she_lo she_hi];
  rewrite UB;
  first [ rewrite (UO 36%nat _ E36) by lia | rewrite (UO 38%nat _ E38) by lia | rewrite (UO 40%nat _ E40) by lia ];
  (split; [eapply range_addressable_sub; [exact HRA | destruct HkN; lia | destruct HkN; lia] |]);
  intros a Ha; cbn [Z.min Z.max] in Ha;
  unfold in_app, kLowShadowBeg, kHighMemBeg, rvs_SB in *; destruct HkN; subst kN; cbn [Z.min Z.max] in Ha; lia.
Qed.
Lemma rvs_entry_f : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  ma mi pa o c lo13 hi13 lo14 hi14,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= spZ regs - REAC_VER_STR_STK -> spZ regs <= sp0 -> spZ regs mod 16 = 0 ->
getr regs 13 = w64 o -> getr regs 14 = w64 c -> lo13 <= o <= hi13 -> lo14 <= c <= hi14 ->
0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
st_ok_pi SEGS VAL (rvs_E regs ma mi pa o) (rvs_ssF lo13 hi13 lo14 hi14)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_identity_reac_ver_str) memc (seg_rom SEGS))) /\
sh_ok SEGS rvs_Bx [] (rvs_E regs ma mi pa o) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c lo13 hi13 lo14 hi14
  HJ Hlo Hhi Hal16 H13 H14 R13 R14 Ro Rc.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_VER_STR_STK = 4224) by reflexivity.
set (E := rvs_E regs ma mi pa o).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rvs_extra ma mi pa o)) n)
  by (intros n Hn; subst E; unfold rvs_E; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U13 : bv_unsigned (ew E 13) = o)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl), H13; apply unsigned_lit_small; exact Ro).
assert (U14 : bv_unsigned (ew E 14) = c)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl), H14; apply unsigned_lit_small; exact Rc).
split; [|constructor].
rewrite restrict_mkst_fx. unfold rvs_ssF, A_reac_identity_reac_ver_str. apply pa_entry_st_ok_full.
- subst E. unfold rvs_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp, U13, U14.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
(* ---- the walk's tactics ---------------------------------------------------------------------- *)
(* The run's write right: the frame is in the caller's window below sp, the image cells are not written,
   and the caller lets the call write the buffer (HWk: awr_byte for each byte of [o, o + 20)). *)
Ltac rvs_awr regs sp0 Usp HWk U36 U38 U40 :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
    [ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; rewrite Usp; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | ]
  | lazymatch goal with |- awr_ok ?E (YP09.mkRegion (Some ?n) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ n (bv_unsigned (ew E n)));
      [ reflexivity | reflexivity
      | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HWk;
        cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb] in Ha; rewrite ?U36, ?U38, ?U40 in Ha; lia | ] end ].
(* A byte the run may have written lies in one of its regions' windows. *)
Ltac rvs_wr H :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  destruct H as (r & Hr & Ha); vm_compute in Hr;
  repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb] in Ha | ]);
  try contradiction.
(* What a run changed: its frame and its regions' windows; the bytes E are the buffer bytes among them. *)
Ltac rvs_piece HFr HG HAR HBY Usp U36 U38 U40 WS lyc Sc W memc mdc :=
  lazymatch type of HFr with frame_of ?E0 ?rs0 _ _ =>
  eapply (rvs_k_of_run lyc Sc W memc mdc); [exact HAR | rewrite WS; lia | lia | | | exact HG];
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hea := fresh "Hea" in intros a Ha Hea;
    let Hni := fresh "Hni" in destruct (HBY a ltac:(lia)) as (_ & _ & Hni); exact (Hni Ha)
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in let He := fresh "He" in
    intros a Ha Hw He; apply (rvs_aview_frame W _ _ (fun x => ~ in_wrange E0 rs0 x) a Ha); [|exact HFr];
    let Hin := fresh "Hin" in intros Hin; rvs_wr Hin; rewrite ?Usp, ?U36, ?U38, ?U40 in *; rewrite WS in Hw;
    first [ lia | exfalso; apply He; lia ] ]
  end.
(* The buffer's shadow is in no window of a run. *)
Ltac rvs_ra_run HFr RA0 Happ Usp U36 U38 U40 C1 :=
  lazymatch type of HFr with frame_of ?E0 ?rs0 (mrestrict _ ?mA) (mrestrict _ ?mB) =>
  apply (rvs_ra_shadow _ _ mA mB _ _ RA0); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  let Hsb := fresh "Hsb" in
  pose proof (YCbq.shadow_addr_bounds x ltac:(unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia)) as Hsb;
  apply (rvs_aview_frame _ _ _ (fun y => ~ in_wrange E0 rs0 y)); [unfold kHighShadowEnd in Hsb; lia | | exact HFr];
  let Hin := fresh "Hin" in intros Hin; rvs_wr Hin; rewrite ?Usp, ?U36, ?U38, ?U40 in *;
  unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *; lia
  end.
(* The n-th region of a state's symbolic memory. *)
Ltac rvs_reg HS n HR :=
  let HRok := fresh "HRok" in pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HRok & _);
  lazymatch type of HRok with Forall (YP09.region_ok _ ?Ek ?mx) ?rs =>
    let rs' := eval vm_compute in rs in
    let r := eval vm_compute in (nth n rs' got_regionP) in
    assert (HR : YP09.region_ok SEGS Ek mx r)
      by (apply (proj1 (Forall_forall _ _) HRok); change rs with rs'; cbn [In]; repeat (first [left; reflexivity | right]))
  end; clear HRok.
(* The regions a write_uint call keeps: the frame (above its stack, below the caller's sp) and the
   buffer bytes outside the bytes it writes. *)
Ltac rvs_kept o Htcj HDk HBYn Hpresn Qsp WU Usp U36 U38 U40 :=
  cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; split;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb];
  rewrite ?Usp, ?U36, ?U38, ?U40; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  first
  [ apply (mbyte_of_aview SEGS); let T1 := fresh "T1" in destruct Htcj as (T1 & _); apply T1;
    [lia | rewrite Qsp, WU; lia | cbv beta; lia]
  | apply (mbyte_of_aview SEGS); apply (rvs_k_byte _ _ _ _ _ _ _ _ _ o 20 a (rvs_k_of_tcj _ _ _ _ _ _ _ _ _ Htcj) HDk);
    [lia | cbv beta; lia]
  | intros _; apply (apresent_writable SEGS); apply Hpresn; lia
  | intros _; apply (apresent_writable SEGS); exact (proj1 (HBYn a ltac:(lia))) ].
(* The shadow entries of the three bytes the walk writes. *)
Ltac rvs_shok RA E32 E36 E38 E40 Happ HkN :=
  unfold sh_ok, rvs_SH; repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart, rvs_Bx;
  cbn [she_m she_lo she_hi]; rewrite !U_SOff; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb];
  rewrite E32, ?E36, ?E38, ?E40, !unsigned_lit_small by (unfold rvs_SB; lia);
  rewrite !Z.add_0_r, !rvs_zc by (unfold rvs_SB; lia);
  (split; [eapply range_addressable_sub; [exact RA | destruct HkN; lia | destruct HkN; lia] |]);
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, rvs_SB in *; destruct HkN; subst; cbn [Z.min Z.max] in Ha; lia.
(* Bytes known at an earlier memory, kept by every later piece. *)
Lemma rvs_garr8_k : forall lyc Sc W1 m1 W2 m2 lo hi (E : Z -> Prop) q n base l,
rvs_k lyc Sc W1 m1 W2 m2 lo hi E -> rvs_dst lyc Sc q n ->
garr8 SEGS (mrestrict (w_H W1) m1) base l ->
q <= base -> base + Z.of_nat (length l) <= q + n ->
(forall a, base <= a < base + Z.of_nat (length l) -> ~ E a) ->
garr8 SEGS (mrestrict (w_H W2) m2) base l.
Proof.
intros lyc Sc W1 m1 W2 m2 lo hi E q n base l HK HD HG Hq1 Hq2 HE.
apply (garr8_frame SEGS _ _ base l HG). intros a Ha. apply (mbyte_of_aview SEGS).
exact (rvs_k_byte _ _ _ _ _ _ _ _ _ q n a HK HD ltac:(lia) (HE a Ha)).
Qed.
Theorem rvs_walk_f : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (ma mi pa o c : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
sp0 - STK <= spZ regs - REAC_VER_STR_STK -> spZ regs <= sp0 ->
getr regs 13 = w64 o -> getr regs 14 = w64 c -> 0 <= o < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> rvs_fails o c = true ->
SRr SEGS W (cfg_at SEGS A_reac_identity_reac_ver_str regs memc mdc)
(treac_identity_reac_ver_str_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs ma mi pa o c).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c HJ Hra Hal16 Hlo Hhi H13 H14 Ro Rc Hf.
pose proof pa_segs_low as Hsegs.
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_VER_STR_STK = 4224) by reflexivity.
assert (Hcase : o = 0 \/ (1 <= o /\ c <= 19)).
{ unfold rvs_fails in Hf. apply orb_true_iff in Hf as [X|X]; [apply Z.eqb_eq in X; left; exact X|].
  apply Z.ltb_lt in X. destruct (Z.eq_dec o 0); [left; assumption | right; lia]. }
destruct Hcase as [O0 | (O1 & C19)];
[ destruct (rvs_entry_f STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c 0 0 0 (2 ^ 64 - 1)
    HJ Hlo Hhi Hal16 H13 H14 ltac:(lia) ltac:(lia) Ro Rc) as [HS0 SHOK];
  pose proof (st_ok_pi_pin_reg' _ _ _ (13%bv : bv 5) 0 HS0
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H13, O0; reflexivity) ltac:(vm_compute; reflexivity)) as HS;
  clear HS0
| destruct (rvs_entry_f STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c 1 (2 ^ 64 - 1) 0 19
    HJ Hlo Hhi Hal16 H13 H14 ltac:(lia) ltac:(lia) Ro Rc) as [HS SHOK] ].
all: remember (rvs_E regs ma mi pa o) as E eqn:HE.
all: assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rvs_E; apply Eimg_env).
all: assert (E1 : ew E 1 = getr regs 1)
  by (subst E; unfold rvs_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
all: assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (subst E; unfold rvs_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
all: assert (HAE : env_agree 32 (Ereg regs (rvs_extra ma mi pa o)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
all: clear HE.
all: unfold cfg_at, A_reac_identity_reac_ver_str in *.
all: change (w64 (BASE + AF_reac_identity_reac_ver_str)) with (Z_to_bv 64 (BASE + AF_reac_identity_reac_ver_str)).
all: unfold treac_identity_reac_ver_str_post; rewrite Hf; cbv beta iota.
all: change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_reac_ver_str)) memc (seg_rom SEGS))) in HJ.
all: paj_run_tok RUN HS HJ SHOK rvs_Bspan; [rvs_awr regs sp0 Usp HJ Usp Usp Usp |].
all: lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat';
  split; [reflexivity|];
  exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite R1, E1, Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); unfold EV_REAC_VER_STR; rewrite Z.add_0_r; exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rvs_extra ma mi pa o) HS); [env_agree_chain HAE | vm_compute; reflexivity]|];
  split; [apply Permutation_refl|]; split; [reflexivity|];
  split; [rewrite R10; unfold w64; exact lit_m1|]
end.
all: lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msf),
  HFr : frame_of ?E0 ?rs0 (mrestrict _ ?m0) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
  eapply rvs_tcj_of_k; [exact HJ | | lia | lia];
  eapply (rvs_k_of_run lyc Sc W memc mdc); [exact HAR | rewrite WS; lia | lia | intros a _ [] | | exact HG];
  let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
  intros a Ha Hw _; apply (rvs_aview_frame W _ _ (fun x => ~ in_wrange E0 rs0 x) a Ha); [|exact HFr];
  let Hin := fresh "Hin" in intros Hin; rvs_wr Hin; rewrite WS in Hw; rewrite Usp in *; lia
end.
Qed.
(* The path that writes; kN, lo12 and hi12 fix which of pa < 10 or 10 <= pa it is. *)
Lemma rvs_walk_w : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (ma mi pa o c kN lo12 hi12 : Z),
(kN = 2 /\ lo12 = 0 /\ hi12 = 9) \/ (kN = 1 /\ lo12 = 10 /\ hi12 = 65535) -> lo12 <= pa <= hi12 ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_VER_STR_STK -> spZ regs <= sp0 ->
getr regs 10 = w64 ma -> getr regs 11 = w64 mi -> getr regs 12 = w64 pa ->
getr regs 13 = w64 o -> getr regs 14 = w64 c ->
0 <= ma < 65536 -> 0 <= mi < 65536 -> 20 <= c < 2 ^ 64 -> rvs_fails o c = false ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 20 -> rvs_dst lyc Sc o 20 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 20 -> Z.of_nat (length (frames Sc)) <= 8 ->
SRr SEGS W (cfg_at SEGS A_reac_identity_reac_ver_str regs memc mdc)
(treac_identity_reac_ver_str_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs ma mi pa o c).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c kN lo12 hi12
  HCASE Rpa HJ Hra Hgp Htp Hal16 Hlo Hhi H10 H11 H12 H13 H14 Rma Rmi Rc Hf HW HD HRA HNF.
pose proof pa_segs_low as Hsegs.
pose proof (proj1 HJ) as HAR. pose proof HJ as HJ0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_VER_STR_STK = 4224) by reflexivity.
assert (WU : write_uint.WRITE_UINT_STK = 4176) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (rvs_n_range ma) as N1. pose proof (rvs_n_range mi) as N2. pose proof (rvs_n_range pa) as N3.
destruct (rvs_dst_facts lyc Sc W memc mdc o 20 HAR HD ltac:(lia)) as (Ho4096 & HoC & Happ & HBY).
assert (HkN : kN = 1 \/ kN = 2) by (destruct HCASE as [(-> & _) | (-> & _)]; auto).
assert (Rlo12 : 0 <= lo12) by (destruct HCASE as [(_ & -> & _) | (_ & -> & _)]; lia).
assert (Rhi12 : hi12 < 65536) by (destruct HCASE as [(_ & _ & ->) | (_ & _ & ->)]; lia).
assert (HLV : rvs_LV ma mi pa = rvs_n ma + rvs_n mi + rvs_n pa + kN).
{ rewrite rvs_LV_eq. destruct HCASE as [(-> & -> & ->) | (-> & -> & ->)].
  - rewrite (proj2 (Z.ltb_lt pa 10)) by lia. rewrite (rvs_n_lt10 pa) by lia. lia.
  - rewrite (proj2 (Z.ltb_ge pa 10)) by lia. lia. }
assert (HW1 : forall a, o <= a < o + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a)
  by (intros a Ha; exact (proj1 (HW a Ha))).
assert (Qs : 0 <= spZ regs - 48 < 2 ^ 64) by lia.
(* The three write_uint calls, from their arguments: the callee's contract (B's write_uint.v) at BASE +
   AF_write_uint, with every premise from the caller's journal, the buffer facts and the entry's twr_ok. *)
assert (CALL : forall ly1 S1 m1 md1 kk (regs1 : bvmap 5 word) q v retk Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W m1 md1 kk ->
  Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) ->
  range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF o 20 ->
  getr regs1 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs1 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  getr regs1 8 = Z_to_bv 64 o -> getr regs1 10 = Z_to_bv 64 q -> getr regs1 11 = Z_to_bv 64 v ->
  0 <= v < 65536 -> o <= q -> q + rvs_n v <= o + 20 ->
  (forall W2 c2, write_uint.twrite_uint_post B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W m1 kk regs1 q v W2 c2 ->
     SRr SEGS W2 c2 Q) ->
  SRr SEGS W (cfg_at SEGS write_uint.A_write_uint regs1 m1 md1) Q).
{ intros ly1 S1 m1 md1 kk regs1 q v retk Q HJ1 Hp1 HRA1 Rra Hrk Hrk2 Rsp Rgp Rtp Rs0 Ra0 Ra1 Rv Hq1 Hq2 HK.
  destruct (rvs_journal_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJ1) as (Hfr1 & Hfa1).
  pose proof (rvs_dst_move lyc Sc ly1 S1 o 20 HD Hp1 Hfr1 Hfa1) as HD1.
  destruct (rvs_dst_facts ly1 S1 W m1 md1 o 20 (proj1 HJ1) HD1 ltac:(lia)) as (_ & _ & _ & HBY1).
  assert (Qsp : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite Rsp; apply unsigned_lit_small; exact Qs).
  pose proof (rvs_n_range v) as Nv.
  eapply SRr_bind; [apply (TWU STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W m1 md1 kk regs1 [] q v HJ1)
    | intros W2 c2 _ HP; exact (HK W2 c2 HP)];
  change (write_uint_c.write_uint_n v) with (rvs_n v).
  - rewrite Rra. apply ret_ok_codeptr_v; lia.
  - unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
  - rewrite Rgp. exact Hgp.
  - rewrite Rtp. exact Htp.
  - left. split; [left; unfold s0Z; rewrite Rs0, unsigned_lit_small by lia; lia | reflexivity].
  - rewrite Qsp. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - rewrite Qsp, WU. lia.
  - rewrite Qsp. lia.
  - rewrite Ra0. reflexivity.
  - rewrite Ra1. reflexivity.
  - exact Rv.
  - intros a Ha.
    split; [exact (rvs_awr_move STK sp0 FP (ablocks B ly S) lyc Sc ly1 S1 own a (HW1 a ltac:(lia)) Hp1 Hfa1)|].
    destruct (HBY1 a ltac:(lia)) as (Hp & Ho & _). split; [exact Hp|]. split; [exact Ho|]. rewrite Qsp, Hes. lia.
  - apply rvs_dst_tdst. exact (rvs_dst_sub ly1 S1 o 20 q (rvs_n v) HD1 Hq1 Hq2).
  - exact (range_addressable_sub _ _ o 20 q (rvs_n v) HRA1 Hq1 Hq2).
  - rewrite Hfr1. exact HNF. }
destruct (rvs_entry_w STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c kN lo12 hi12
  HJ Hlo Hhi Hal16 H10 H11 H12 H13 H14 Rma Rmi Rlo12 Rpa Rhi12 Rc HkN HD HRA) as [HS SHOK].
remember (rvs_E regs ma mi pa o) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rvs_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rvs_extra ma mi pa o)) n)
  by (intros n Hn; subst E; unfold rvs_E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ma) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 mi) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 pa) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 rvs_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rvs_n ma)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (rvs_n mi)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (rvs_n pa)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (o + rvs_n ma)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (rvs_n ma + rvs_n mi)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (o + rvs_n ma + rvs_n mi)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (rvs_n ma + rvs_n mi + rvs_n pa)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (o + rvs_n ma + rvs_n mi + rvs_n pa)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U36 : bv_unsigned (ew E 36) = o + rvs_n ma) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = o + rvs_n ma + rvs_n mi) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E 40) = o + rvs_n ma + rvs_n mi + rvs_n pa) by (rewrite E40; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (rvs_extra ma mi pa o)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE EL.
unfold cfg_at, A_reac_identity_reac_ver_str in *.
change (w64 (BASE + AF_reac_identity_reac_ver_str)) with (Z_to_bv 64 (BASE + AF_reac_identity_reac_ver_str)).
unfold treac_identity_reac_ver_str_post; rewrite Hf; cbv beta iota.
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_reac_ver_str)) memc (seg_rom SEGS))) in HJ.
destruct HCASE as [(Ek & El & Eh) | (Ek & El & Eh)]; subst lo12 hi12; rewrite Ek in HS, SHOK.
(* ---- run 1: the frame, the shadow base, up to the first call (0x84090) ---- *)
all: paj_run_tok RUN HS HJ SHOK rvs_Bspan; [rvs_awr regs sp0 Usp HW1 U36 U38 U40 |].
all: rename ms into ms1; rename HFr into HFr1; rename HG into HG1; clear HF.
all: assert (K1 : rvs_k lyc Sc W memc W (ms_mem ms1) (spZ regs - REAC_VER_STR_STK) (spZ regs)
  (fun a => a = o + rvs_n ma \/ a = o + rvs_n ma + rvs_n mi + 1 \/ a = o + rvs_n ma + rvs_n mi + rvs_n pa + kN))
  by (rvs_piece HFr1 HG1 HAR HBY Usp U36 U38 U40 WS lyc Sc W memc mdc).
all: assert (RA1 : range_addressable (aview SEGS (w_H W) (ms_mem ms1)) SHADOW_OFF o 20)
  by (rvs_ra_run HFr1 HRA Happ Usp U36 U38 U40 C1).
(* ---- call 1: write_uint (o, ma) ---- *)
all: pmkst HS.
all: rewrite (PSIG IS_write_uint AF_write_uint eq_refl).
all: prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
  prreg HS (8%bv : bv 5) Rs0; prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1.
all: rewrite Usp in Rsp; rewrite E3 in Rgp; rewrite E4 in Rtp; rewrite E13 in Rs0, Ra0; rewrite E10 in Ra1.
all: replace (spZ regs + -48) with (spZ regs - 48) in Rsp by lia.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS write_uint.A_write_uint rg mm mdx) Q) end.
all: eapply (CALL _ _ _ _ _ _ o ma 14728 _ HJ (Permutation_refl _) RA1 Rra ltac:(lia) eq_refl Rsp Rgp Rtp Rs0 Ra0 Ra1
  Rma ltac:(lia) ltac:(lia)).
all: intros W2 c2 (-> & lyA & SA & regsA & memA & mdA & -> & HJA & HPA & Ha0A & HpermA & HgarA & HtcjA).
all: fold (rvs_n ma) in Ha0A, HtcjA.
all: destruct (rvs_journal_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJA) as (HfrA & HfaA).
all: pose proof (rvs_dst_move lyc Sc lyA SA o 20 HD HpermA HfrA HfaA) as HDA.
all: destruct (rvs_dst_facts lyA SA W memA mdA o 20 (proj1 HJA) HDA ltac:(lia)) as (_ & _ & _ & HBYA).
all: pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresA & _).
all: assert (Qsp1 : spZ (ms_regs ms1) = spZ regs - 48) by (unfold spZ at 1; rewrite Rsp; apply unsigned_lit_small; exact Qs).
all: assert (KA : rvs_k lyc Sc W (ms_mem ms1) W memA (spZ regs - REAC_VER_STR_STK) (spZ regs)
  (fun a => o <= a < o + rvs_n ma))
  by (pose proof (rvs_k_of_tcj _ _ _ _ _ _ _ _ _ HtcjA) as X; rewrite Qsp1, WU in X;
      eapply rvs_k_mono; [exact X | rewrite WS; lia | lia | intros a Ha; exact Ha]).
all: assert (RAA : range_addressable (aview SEGS (w_H W) memA) SHADOW_OFF o 20)
  by (eapply (rvs_ra_call _ lyc Sc lyA SA W (ms_mem ms1) memA _ mdA);
      [exact (proj1 HJ) | exact (proj1 HJA) | exact HpermA | exact HD | lia | exact Happ | exact RA1 | exact HtcjA
      | intros a Ha; cbv beta in Ha; lia]).
all: jafter_call_keep_pi HS 41%nat regsA (mrestrict (w_H W) memA) HPA [0; 3; 4; 5]%nat HS2.
all: match type of HS2 with ?tq -> _ => assert (HRK : tq) by (rvs_kept o HtcjA HD HBYA HpresA Qsp1 WU Usp U36 U38 U40);
  specialize (HS2 HRK); clear HRK end.
all: rewrite <- restrict_mkst_fx in HS2. all: rewrite Rra.
all: pose proof (rvs_pin _ _ _ (10%bv : bv 5) 33%nat HS2
  ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0A; unfold w64; apply bv_eq; rewrite denot_SOff, unsigned_lit_small by lia;
        cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; rewrite E33, unsigned_lit_small, Z.add_0_r, rvs_zc by lia; reflexivity)
  ltac:(vm_compute; reflexivity)) as HS3.
all: clear HS2 HS; rename HS3 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEIa : img_env VAL A_LIM E2) by (apply img_env_havoc; [assumption | cbv; lia]) end.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
all: clear SHOK; lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (SHOK : sh_ok SEGS rvs_Bx (rvs_SH kN) E2 (mrestrict (w_H W) memA)) by (rvs_shok RAA E32 E36 E38 E40 Happ HkN) end.
all: rewrite Ek in SHOK.
all: assert (HW2 : forall a, o <= a < o + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyA SA) lyA own a)
  by (intros a Ha; exact (rvs_awr_move STK sp0 FP (ablocks B ly S) lyc Sc lyA SA own a (HW1 a Ha) HpermA HfaA)).
(* ---- run 2: '.' at o + n1, up to the second call (0x840c0) ---- *)
all: paj_run_tok RUN HS HJA SHOK rvs_Bspan; [rvs_awr regs sp0 Usp HW2 U36 U38 U40 |].
all: rename ms into ms2; rename HFr into HFr2; rename HG into HG2; clear HF.
all: rvs_reg HS 1%nat HRD.
all: assert (GD : garr8 SEGS (mrestrict (w_H W) (ms_mem ms2)) (o + rvs_n ma + 0) [46])
  by (apply (rvs_byte_reg _ _ 36 0 1 0 1 0 (SLit 46) 46 _ HRD);
      [cbn [base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact U36 | vm_compute; reflexivity]).
all: clear HRD.
all: assert (K2 : rvs_k lyc Sc W memA W (ms_mem ms2) (spZ regs - REAC_VER_STR_STK) (spZ regs)
  (fun a => a = o + rvs_n ma \/ a = o + rvs_n ma + rvs_n mi + 1 \/ a = o + rvs_n ma + rvs_n mi + rvs_n pa + kN))
  by (rvs_piece HFr2 HG2 HAR HBY Usp U36 U38 U40 WS lyc Sc W memc mdc).
all: assert (RA2 : range_addressable (aview SEGS (w_H W) (ms_mem ms2)) SHADOW_OFF o 20)
  by (rvs_ra_run HFr2 RAA Happ Usp U36 U38 U40 C1).
(* ---- call 2: write_uint (o + n1 + 1, mi) ---- *)
all: clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra1.
all: pmkst HS.
all: rewrite (PSIG IS_write_uint AF_write_uint eq_refl).
all: prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
  prreg HS (8%bv : bv 5) Rs0; prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1.
all: rewrite Usp in Rsp; rewrite E3 in Rgp; rewrite E4 in Rtp; rewrite E13 in Rs0; rewrite U36 in Ra0; rewrite E11 in Ra1.
all: replace (spZ regs + -48) with (spZ regs - 48) in Rsp by lia.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS write_uint.A_write_uint rg mm mdx) Q) end.
all: eapply (CALL _ _ _ _ _ _ (o + rvs_n ma + 1) mi 14776 _ HJA HpermA RA2 Rra ltac:(lia) eq_refl Rsp Rgp Rtp Rs0 Ra0 Ra1
  Rmi ltac:(lia) ltac:(lia)).
all: intros W2 c2 (-> & lyB & SB & regsB & memB & mdB & -> & HJB & HPB & Ha0B & HpermB & HgarB & HtcjB).
all: fold (rvs_n mi) in Ha0B, HtcjB.
all: pose proof (Permutation_trans HpermB HpermA) as HpermBc.
all: destruct (rvs_journal_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJB) as (HfrB & HfaB).
all: pose proof (rvs_dst_move lyc Sc lyB SB o 20 HD HpermBc HfrB HfaB) as HDB.
all: destruct (rvs_dst_facts lyB SB W memB mdB o 20 (proj1 HJB) HDB ltac:(lia)) as (_ & _ & _ & HBYB).
all: pose proof HJB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresB & _).
all: assert (Qsp2 : spZ (ms_regs ms2) = spZ regs - 48) by (unfold spZ at 1; rewrite Rsp; apply unsigned_lit_small; exact Qs).
all: assert (KB : rvs_k lyc Sc W (ms_mem ms2) W memB (spZ regs - REAC_VER_STR_STK) (spZ regs)
  (fun a => o + rvs_n ma + 1 <= a < o + rvs_n ma + 1 + rvs_n mi))
  by (pose proof (rvs_k_of_tcj _ _ _ _ _ _ _ _ _ HtcjB) as X; rewrite Qsp2, WU in X;
      eapply (rvs_k_move lyc Sc lyA SA); [|exact HpermA | exact HfrA | exact HfaA];
      eapply rvs_k_mono; [exact X | rewrite WS; lia | lia | intros a Ha; exact Ha]).
all: assert (RAB : range_addressable (aview SEGS (w_H W) memB) SHADOW_OFF o 20)
  by (eapply (rvs_ra_call _ lyA SA lyB SB W (ms_mem ms2) memB _ mdB);
      [exact (proj1 HJA) | exact (proj1 HJB) | exact HpermB | exact HDA | lia | exact Happ | exact RA2 | exact HtcjB
      | intros a Ha; cbv beta in Ha; lia]).
all: jafter_call_keep_pi HS 57%nat regsB (mrestrict (w_H W) memB) HPB [0; 2; 3]%nat HS2.
all: match type of HS2 with ?tq -> _ => assert (HRK : tq) by (rvs_kept o HtcjB HDA HBYB HpresB Qsp2 WU Usp U36 U38 U40);
  specialize (HS2 HRK); clear HRK end.
all: rewrite <- restrict_mkst_fx in HS2. all: rewrite Rra.
all: pose proof (rvs_pin _ _ _ (10%bv : bv 5) 34%nat HS2
  ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0B; unfold w64; apply bv_eq; rewrite denot_SOff, unsigned_lit_small by lia;
        cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; rewrite E34, unsigned_lit_small, Z.add_0_r, rvs_zc by lia; reflexivity)
  ltac:(vm_compute; reflexivity)) as HS3.
all: clear HS2 HS; rename HS3 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEIb : img_env VAL A_LIM E2) by (apply img_env_havoc; [assumption | cbv; lia]) end.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
all: clear SHOK; lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (SHOK : sh_ok SEGS rvs_Bx (rvs_SH kN) E2 (mrestrict (w_H W) memB)) by (rvs_shok RAB E32 E36 E38 E40 Happ HkN) end.
all: rewrite Ek in SHOK.
all: assert (HW3 : forall a, o <= a < o + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyB SB) lyB own a)
  by (intros a Ha; exact (rvs_awr_move STK sp0 FP (ablocks B ly S) lyc Sc lyB SB own a (HW1 a Ha) HpermBc HfaB)).
(* ---- run 3: the padding '0' when pa < 10, up to the third call ---- *)
all: paj_run_tok RUN HS HJB SHOK rvs_Bspan; [rvs_awr regs sp0 Usp HW3 U36 U38 U40 |].
all: rename ms into ms3; rename HFr into HFr3; rename HG into HG3; clear HF.
1: rvs_reg HS 1%nat HRP.
1: assert (GP : garr8 SEGS (mrestrict (w_H W) (ms_mem ms3)) (o + rvs_n ma + rvs_n mi + 1) [48])
  by (apply (rvs_byte_reg _ _ 38 1 2 1 2 1 (SLit 48) 48 _ HRP);
      [cbn [base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact U38 | vm_compute; reflexivity]).
1: clear HRP.
all: assert (K3 : rvs_k lyc Sc W memB W (ms_mem ms3) (spZ regs - REAC_VER_STR_STK) (spZ regs)
  (fun a => a = o + rvs_n ma + rvs_n mi + 1 \/ a = o + rvs_n ma + rvs_n mi + rvs_n pa + kN))
  by (rvs_piece HFr3 HG3 HAR HBY Usp U36 U38 U40 WS lyc Sc W memc mdc).
all: assert (RA3 : range_addressable (aview SEGS (w_H W) (ms_mem ms3)) SHADOW_OFF o 20)
  by (rvs_ra_run HFr3 RAB Happ Usp U36 U38 U40 C1).
(* ---- call 3: write_uint (o + n1 + 1 + n2 (+ 1 when pa < 10), pa) ---- *)
all: clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra1.
all: pmkst HS.
all: rewrite (PSIG IS_write_uint AF_write_uint eq_refl).
all: prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
  prreg HS (8%bv : bv 5) Rs0; prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1.
all: rewrite Usp in Rsp; rewrite E3 in Rgp; rewrite E4 in Rtp; rewrite E13 in Rs0; rewrite U38 in Ra0; rewrite E12 in Ra1.
all: replace (spZ regs + -48) with (spZ regs - 48) in Rsp by lia.
all: assert (Ra0' : getr (ms_regs ms3) 10 = Z_to_bv 64 (o + rvs_n ma + rvs_n mi + kN)) by (rewrite Ra0, Ek; reflexivity).
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS write_uint.A_write_uint rg mm mdx) Q) end.
all: eapply (CALL _ _ _ _ _ _ (o + rvs_n ma + rvs_n mi + kN) pa 14832 _ HJB HpermBc RA3 Rra ltac:(lia) eq_refl
  Rsp Rgp Rtp Rs0 Ra0' Ra1 ltac:(lia) ltac:(lia) ltac:(lia)).
all: intros W2 c2 (-> & lyC & SC & regsC & memC & mdC & -> & HJC & HPC & Ha0C & HpermC & HgarC & HtcjC).
all: fold (rvs_n pa) in Ha0C, HtcjC.
all: pose proof (Permutation_trans HpermC HpermBc) as HpermCc.
all: destruct (rvs_journal_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJC) as (HfrC & HfaC).
all: pose proof (rvs_dst_move lyc Sc lyC SC o 20 HD HpermCc HfrC HfaC) as HDC.
all: destruct (rvs_dst_facts lyC SC W memC mdC o 20 (proj1 HJC) HDC ltac:(lia)) as (_ & _ & _ & HBYC).
all: pose proof HJC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresC & _).
all: assert (Qsp3 : spZ (ms_regs ms3) = spZ regs - 48) by (unfold spZ at 1; rewrite Rsp; apply unsigned_lit_small; exact Qs).
all: assert (KC : rvs_k lyc Sc W (ms_mem ms3) W memC (spZ regs - REAC_VER_STR_STK) (spZ regs)
  (fun a => o + rvs_n ma + rvs_n mi + kN <= a < o + rvs_n ma + rvs_n mi + kN + rvs_n pa))
  by (pose proof (rvs_k_of_tcj _ _ _ _ _ _ _ _ _ HtcjC) as X; rewrite Qsp3, WU in X;
      eapply (rvs_k_move lyc Sc lyB SB); [|exact HpermBc | exact HfrB | exact HfaB];
      eapply rvs_k_mono; [exact X | rewrite WS; lia | lia | intros a Ha; exact Ha]).
all: assert (RAC : range_addressable (aview SEGS (w_H W) memC) SHADOW_OFF o 20)
  by (eapply (rvs_ra_call _ lyB SB lyC SC W (ms_mem ms3) memC _ mdC);
      [exact (proj1 HJB) | exact (proj1 HJC) | exact HpermC | exact HDB | lia | exact Happ | exact RA3 | exact HtcjC
      | intros a Ha; cbv beta in Ha; lia]).
all: jafter_call_keep_pi HS 73%nat regsC (mrestrict (w_H W) memC) HPC [0; 2]%nat HS2.
all: match type of HS2 with ?tq -> _ => assert (HRK : tq) by (rvs_kept o HtcjC HDB HBYC HpresC Qsp3 WU Usp U36 U38 U40);
  specialize (HS2 HRK); clear HRK end.
all: rewrite <- restrict_mkst_fx in HS2. all: rewrite Rra.
all: pose proof (rvs_pin _ _ _ (10%bv : bv 5) 35%nat HS2
  ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0C; unfold w64; apply bv_eq; rewrite denot_SOff, unsigned_lit_small by lia;
        cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; rewrite E35, unsigned_lit_small, Z.add_0_r, rvs_zc by lia; reflexivity)
  ltac:(vm_compute; reflexivity)) as HS3.
all: clear HS2 HS; rename HS3 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEIc : img_env VAL A_LIM E2) by (apply img_env_havoc; [assumption | cbv; lia]) end.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
all: clear SHOK; lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (SHOK : sh_ok SEGS rvs_Bx (rvs_SH kN) E2 (mrestrict (w_H W) memC)) by (rvs_shok RAC E32 E36 E38 E40 Happ HkN) end.
all: rewrite Ek in SHOK.
all: assert (HW4 : forall a, o <= a < o + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyC SC) lyC own a)
  by (intros a Ha; exact (rvs_awr_move STK sp0 FP (ablocks B ly S) lyc Sc lyC SC own a (HW1 a Ha) HpermCc HfaC)).
(* ---- run 4: the NUL at o + LV and the return ---- *)
all: paj_run_tok RUN HS HJC SHOK rvs_Bspan; [rvs_awr regs sp0 Usp HW4 U36 U38 U40 |].
all: rename ms into ms4; rename HFr into HFr4; rename HG into HG4; clear HF.
all: rvs_reg HS 1%nat HRN.
all: assert (GN : garr8 SEGS (mrestrict (w_H W) (ms_mem ms4)) (o + rvs_n ma + rvs_n mi + rvs_n pa + kN) [0])
  by (rewrite Ek; apply (rvs_byte_reg _ _ 40 _ _ _ _ _ (SLit 0) 0 _ HRN);
      [cbn [base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact U40 | vm_compute; reflexivity]).
all: clear HRN.
all: assert (K4 : rvs_k lyc Sc W memC W (ms_mem ms4) (spZ regs - REAC_VER_STR_STK) (spZ regs)
  (fun a => a = o + rvs_n ma + rvs_n mi + rvs_n pa + kN))
  by (rvs_piece HFr4 HG4 HAR HBY Usp U36 U38 U40 WS lyc Sc W memc mdc).
(* ---- the return and the post-condition ---- *)
all: unfold write_uint.EV_WRITE_UINT in HJC; rewrite !Z.add_0_r in HJC.
all: pose proof (rvs_k_trans _ _ _ _ _ _ _ _ _ _ _ _ KC K4) as KC4.
all: pose proof (rvs_k_trans _ _ _ _ _ _ _ _ _ _ _ _ K3 KC4) as K34.
all: pose proof (rvs_k_trans _ _ _ _ _ _ _ _ _ _ _ _ KB K34) as KB4.
all: pose proof (rvs_k_trans _ _ _ _ _ _ _ _ _ _ _ _ K2 KB4) as K24.
all: pose proof (rvs_k_trans _ _ _ _ _ _ _ _ _ _ _ _ KA K24) as KA4.
all: pose proof (rvs_k_trans _ _ _ _ _ _ _ _ _ _ _ _ K1 KA4) as K14.
all: clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra1 Ra0'.
(* the value returned: the sum n1 + kN + n2 + n3, which is LV *)
all: lazymatch goal with HS : st_ok_pi _ _ ?Ef _ _ |- _ =>
  assert (UG33 : bv_unsigned (ew Ef 33) = rvs_n ma)
    by (cbn [ew havoc ewset Nat.eqb Nat.ltb Nat.leb]; rewrite E33; apply unsigned_lit_small; lia);
  assert (UG34 : bv_unsigned (ew Ef 34) = rvs_n mi)
    by (cbn [ew havoc ewset Nat.eqb Nat.ltb Nat.leb]; rewrite E34; apply unsigned_lit_small; lia);
  assert (UG35 : bv_unsigned (ew Ef 35) = rvs_n pa)
    by (cbn [ew havoc ewset Nat.eqb Nat.ltb Nat.leb]; rewrite E35; apply unsigned_lit_small; lia)
end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict ?Hh ?msf) |- _ =>
  pose proof (st_ok_pi_restrict_reg Hh Ef ssf msf (10%bv : bv 5) HS) as R10;
  let e := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e in R10;
  cbn [ms_regs restrict mkst] in R10;
  prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat';
  split; [reflexivity|];
  exists lyC, SC, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite R1, E1, Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); unfold EV_REAC_VER_STR; rewrite Z.add_0_r; exact HJC|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rvs_extra ma mi pa o) HS); [env_agree_chain HAE | vm_compute; reflexivity]|];
  split; [exact HpermCc|]; split; [exact HfrC|];
  split; [cbn [ms_regs]; rewrite R10, denot_lit_U; unfold w64; f_equal;
          rewrite ?U_SAlu; cbn [zalu_raw]; rewrite !U_SOff; rewrite ?UG33, ?UG34, ?UG35;
          rvs_zcs; rewrite HLV, Ek; lia|]
end.
all: split.
(* what the call kept: every piece's bytes are in [o, o + LV + 1) *)
2,4: eapply rvs_tcj_of_k;
  [ exact HJC | eapply rvs_k_mono; [exact K14 | lia | lia | intros a Ha; cbv beta in Ha |- *; rewrite HLV; lia]
  | lia | lia ].
(* the bytes: write_uint's digits of ma, '.', the digits of mi, ('0' when pa < 10,) the digits of pa, the NUL *)
all: rewrite (rvs_bytes_split ma mi pa ltac:(lia)).
1: rewrite (proj2 (Z.ltb_lt pa 10)) by lia. 2: rewrite (proj2 (Z.ltb_ge pa 10)) by lia; rewrite app_nil_l.
all: cbv beta iota.
all: apply garr8_app; split;
  [ eapply (rvs_garr8_k _ _ _ _ _ _ _ _ _ o 20 _ _ K24 HD HgarA); rewrite ?rvs_wu_len; [lia | lia | intros a Ha; cbv beta; lia] |].
all: rewrite rvs_wu_len; apply garr8_app; split;
  [ rewrite Z.add_0_r in GD; eapply (rvs_garr8_k _ _ _ _ _ _ _ _ _ o 20 _ _ KB4 HD GD);
    cbn [length Z.of_nat Pos.of_succ_nat]; [lia | lia | intros a Ha; cbv beta; lia] |].
all: change (Z.of_nat (length [46])) with 1; apply garr8_app; split;
  [ eapply (rvs_garr8_k _ _ _ _ _ _ _ _ _ o 20 _ _ K34 HD HgarB); rewrite ?rvs_wu_len; [lia | lia | intros a Ha; cbv beta; lia] |].
all: rewrite rvs_wu_len; apply garr8_app; split.
1: apply garr8_app; split;
  [ replace (o + rvs_n ma + 1 + rvs_n mi) with (o + rvs_n ma + rvs_n mi + 1) by lia;
    eapply (rvs_garr8_k _ _ _ _ _ _ _ _ _ o 20 _ _ KC4 HD GP); cbn [length Z.of_nat Pos.of_succ_nat];
    [lia | lia | intros a Ha; cbv beta; lia]
  | match goal with |- garr8 _ _ ?b _ => replace b with (o + rvs_n ma + rvs_n mi + kN) by (cbn [length Z.of_nat Pos.of_succ_nat]; lia) end;
    eapply (rvs_garr8_k _ _ _ _ _ _ _ _ _ o 20 _ _ K4 HD HgarC); rewrite ?rvs_wu_len; [lia | lia | intros a Ha; cbv beta; lia] ].
2: replace (o + rvs_n ma + 1 + rvs_n mi) with (o + rvs_n ma + rvs_n mi + kN) by lia;
  eapply (rvs_garr8_k _ _ _ _ _ _ _ _ _ o 20 _ _ K4 HD HgarC); rewrite ?rvs_wu_len; [lia | lia | intros a Ha; cbv beta; lia].
all: match goal with |- garr8 _ _ ?b _ =>
  replace b with (o + rvs_n ma + rvs_n mi + rvs_n pa + kN)
    by (pose proof (rvs_wu_len pa); rewrite ?length_app in *; cbn [length] in *; lia) end; exact GN.
Qed.
Theorem pb_reac_identity_reac_ver_str : treac_identity_reac_ver_str_spec.
Proof.
unfold treac_identity_reac_ver_str_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c
  HJ Hra Hra4 Hgp Htp Hal16 Hlo Hhi H10 H11 H12 H13 H14 Rma Rmi Rpa Ro Rc HBUF HNF.
destruct (rvs_fails o c) eqn:Hf.
- exact (rvs_walk_f STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c HJ Hra Hal16 Hlo Hhi H13 H14 Ro Rc Hf).
- destruct (HBUF eq_refl) as (HW & HD & HRA).
  assert (Hc20 : 20 <= c) by (unfold rvs_fails in Hf; apply orb_false_iff in Hf as [_ X]; apply Z.ltb_ge in X; exact X).
  destruct (Z.ltb_spec pa 10) as [Hp | Hp].
  + exact (rvs_walk_w STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c 2 0 9
      (or_introl (conj eq_refl (conj eq_refl eq_refl))) ltac:(lia) HJ Hra Hgp Htp Hal16 Hlo Hhi H10 H11 H12 H13 H14
      Rma Rmi ltac:(lia) Hf HW HD HRA HNF).
  + exact (rvs_walk_w STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ma mi pa o c 1 10 65535
      (or_intror (conj eq_refl (conj eq_refl eq_refl))) ltac:(lia) HJ Hra Hgp Htp Hal16 Hlo Hhi H10 H11 H12 H13 H14
      Rma Rmi ltac:(lia) Hf HW HD HRA HNF).
Qed.
End h.
End f.
End d.
