(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module paths and addresses changed; 548 of its 622 lines of code are new or changed and 516 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKeyB.v at a529a88a618 (its key block
   pa_key with the helper lemmas pa_k_find / pa_k_slot / pa_k_bytes_b / pa_k_bytes / pa_k_land3 / pa_k_land16 /
   pa_k_atoms_app / pa_k_alias_app, each with the prefix hbp_k_) and
   proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_key, here hbp_piece_key) for reac-pw/fuzz_headamp's image B: image B's own instructions walked again
   (the first block, its length cell and that cell's shadow address read from the R-relative cells R+0x148 /
   R+0x138 / R+0x150 instead of registers, the three UBSan tests of each pod_put32, the key kept in a5 and the
   length cell's address in s2, and no size-word offset cell written), the cut states and the piece statement of
   lib/AU/HPgSeg.v, and HPgSteps' hdu_blk_postE in place of pa_post. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on its
   unstripped twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id):
   the key piece of one property of the property loop of LLVMFuzzerTestOneInput (0x80c40), SELK 0x81590 ->
   SELS 0x816fc (a params Struct is opened) / SELI 0x828ec (the property's value is an Int pod), as the block
   lemma hbp_key and the piece lemma hbp_piece_key : HPgSeg.hsu_piece_W4_key_stmt at headamp_himg_B /
   headamp_bld_B. Proves no function (kind: segment lemma).

   THE CODE (0x81590 .. 0x816f8, and the out-of-line blocks 0x82b0c .. 0x82b24 and 0x82b84 .. 0x82ba0, which are
   never entered). It is pod.h:175-193 twice (pod_put32(pp, key) then pod_put32(pp, 0)) and then pod.h:407-423:
     0x81590 andi a3,a1,3 (a1 = the selector byte); ld a5,0xb0(s1) = 0x80001; ld s2,0x138(s1) = &pp->len;
     ld t1,0xa8(s1) = -0x4001; bnez a3; 0x815a4 ld a5,0x70(s1) = 0x10003 -- a5 is the key the selector chooses.
     Each of the three instrumented checks of &pp->len (0x815a8, 0x81630, 0x816b0) reads the shadow address the
     build precomputed into R+0x150 (`ld a0,0x150(s1); lbu a0,0(a0); beqz a0`), not an srli / add of its own.
     Each put: the capacity guard `add a2,a0,R+0x108 (-0x3ffd); bltu a2,t1 (-0x4001)` (not taken: the length is
     at most 5440), the two UBSan tests `bltu a0,a4 (0x4001)` and `bgeu a2 (~pp from R+0xf0),a0` (both decided by
     the length bound and pp + PP_SIZE <= 2 ^ 63; their other arm reaches the trap `unimp` 0x83a14), the shadow
     checks of pp + len and pp + len + 3 (base s11), the four byte stores, and len += 4 through s2.
     0x816cc mv a4,s4; beqz a3; li a4,1 leave a4 = if sel mod 4 =? 0 then seen else 1.
     0x816d8 snez a0,a3; seqz a2,s4; and a0,a0,a2; sd a0,0x140(s1) leave R+0x140 = if sel mod 4 =? 0 then 0 else
     1 - seen. 0x816e8 bnez a3 / j 0x828ec (SELI when sel mod 4 = 0); 0x816f0 andi a1,a1,16; beqz a1 -> SELS
     0x816fc, else j 0x828ec (SELI).

   REGISTERS AND R-CELLS (for a port to another image by a register / slot map). Reads: s1 = R (x9),
   s4 = seen (x20), s11 = K (x27), a1 = the selector byte (x11), and the cells R+0x70 (SPA_PROP_VOLUME 0x10003),
   R+0xa8 (-0x4001), R+0xb0 (SPA_PROP_params 0x80001), R+0xf0 (~pp), R+0x108 (-0x3ffd), R+0x138 (&pp->len),
   R+0x148 (pp) and R+0x150 (the shadow address of &pp->len). Writes: a0, a1, a2, a3, a4, a5, a6 (x10 .. x16),
   t1 (x6), s2 (x18), the cell R+0x140, the length cell pp + 0x4000 and the eight bytes of pp at the old length.
   At SELS it also leaves t1 = -0x4001, s2 = &pp->len and s7 = -8 (s7 is not written: SELK already holds it).
   The cells of HPgSeg.hsu_Kc all lie outside [R+0x140, R+0x148), so every one of them is kept.

   THE ROUTE is role's image-A pa_key: the eight bytes at pp + len are one write region over an atom tied to
   pp + len by an alias fact, the length cell another, the R-cells a third, and one shadow entry over pp's whole
   block (19744 bytes, a multiple of 8, so every shadow byte of it is 0) decides every instrumented check on its
   first test. Image B differs in the precomputed shadow address above, in its UBSan tests, in reloading pp for
   the second put (a second alias fact), and in keeping the key in a5 and the length cell's address in s2. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg HPgPropKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ===================================== the entry state of 0x81590 =====================================
   Env slots: 0 .. 31 the registers (9 = R, 11 = the selector byte, 20 = seen, 27 = K), 32 the shadow offset
   (unused here: the shadow base is the register s11), then 33 = pp, 34 = the length, 35 = ~pp, 36 = pp + len,
   37 = sel mod 4 (only when it is not 0), 38 = len - 0x3ffd and 39 = len + 4 - 0x3ffd (the two capacity tests:
   the engine's ranges cannot carry a negative offset of atom 34, so each sum is tied to its own atom). *)
Definition HBP_PPHI : Z := 140737479946976.           (* alloc_ceiling's top minus the block's 19744 bytes *)
Definition HBP_M4001 : Z := 18446744073709535231.     (* -0x4001 mod 2 ^ 64 *)
Definition HBP_M3FFD : Z := 18446744073709535235.     (* -0x3ffd mod 2 ^ 64 *)
Definition hbp_k_x (pp plen sel : Z) : list Z :=
[pp; plen; - pp - 1; pp + plen; sel mod 4; plen - 16381; plen - 16377].
(* the shadow base is s11 (x27); the shadow entry is pp's whole block and the 16 bytes from pp + len *)
Definition hbp_k_Bx : sv := SOff 27 0.
Definition hbp_k_SH : list shent := [mkSHE 33 0 19744; mkSHE 36 0 16].
(* the shadow address of &pp->len, as the build left it in R+0x150 *)
Definition hbp_k_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0x4000) (SLit 3)) (SOff 27 0).
Definition hbp_k_atoms (s : Z) : list (nat * afact) :=
[ (9%nat, mkAF 70368744177664 140737488355328 4); (11%nat, mkAF 0 255 0); (20%nat, mkAF s s 0);
  (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (33%nat, mkAF 4096 HBP_PPHI 4); (34%nat, mkAF 0 5424 0);
  (35%nat, mkAF 18446603336229604639 18446744073709547519 0);
  (36%nat, mkAF 4096 140737479952400 0);
  (38%nat, mkAF 18446744073709535235 18446744073709540659 0);
  (39%nat, mkAF 18446744073709535239 18446744073709540663 0) ].
(* the case: z3 = (sel mod 4 =? 0), b4 = bit 4 of the selector *)
Definition hbp_k_ex (z3 : bool) : list (nat * afact) := if z3 then [] else [(37%nat, mkAF 1 3 0)].
Definition hbp_k_al (z3 b4 : bool) : list (sv * sv) :=
[ (SAlu ALU_AND (SOff 11 0) (SLit 3), if z3 then SLit 0 else SOff 37 0);
  (SAlu ALU_AND (SOff 11 0) (SLit 16), SLit (if b4 then 16 else 0)) ].
Definition hbp_k_al0 : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 33 0) (SOff 34 0), SOff 36 0);
  (SAlu ALU_ADD (SOff 33 0) (SOff 34 4), SOff 36 4);
  (SOff 34 (-16381), SOff 38 0); (SOff 34 (-16377), SOff 39 0) ].
Definition hbp_k_facts (z3 b4 : bool) (s : Z) : facts :=
mkFacts (hbp_k_atoms s ++ hbp_k_ex z3) [] (hbp_k_al0 ++ hbp_k_al z3 b4).
(* the R-relative cells the block reads, with its one R-relative write window [R+0x140, R+0x148) *)
Definition hbp_k_slot_r : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x70 0x158 0x140 0x148
[ YP09.mkChunk 0x70 (CVal 8 (SLit 0x10003)); YP09.mkChunk 0xa8 (CVal 8 (SLit HBP_M4001));
  YP09.mkChunk 0xb0 (CVal 8 (SLit 0x80001)); YP09.mkChunk 0xf0 (CVal 8 (SOff 35 0));
  YP09.mkChunk 0x108 (CVal 8 (SLit HBP_M3FFD)); YP09.mkChunk 0x138 (CVal 8 (SOff 33 0x4000));
  YP09.mkChunk 0x148 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x150 (CVal 8 hbp_k_shx) ].
Definition hbp_k_len_r : YP09.region :=
YP09.mkRegion (Some 33%nat) 0x4000 0x4008 0x4000 0x4008 [ YP09.mkChunk 0x4000 (CVal 8 (SOff 34 0)) ].
Definition hbp_k_buf_r : YP09.region := YP09.mkRegion (Some 36%nat) 0 8 0 8 [].
Definition hbp_k_ss (z3 b4 : bool) (s : Z) : sstate :=
mkSS HBP_SELK sr_atoms [hbp_k_slot_r; hbp_k_len_r; hbp_k_buf_r] None (hbp_k_facts z3 b4 s).

(* ---- small arithmetic ---- *)
Lemma hbp_k_land3 : forall a, Z.land a 3 = a mod 4.
Proof. intros a. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma hbp_k_land16 : forall a, Z.land a 16 = if Z.testbit a 4 then 16 else 0.
Proof.
intros a. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
change 16 with (2 ^ 4). rewrite Z.pow2_bits_eqb by lia.
destruct (Z.testbit a 4) eqn:Hb.
- rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 4 i) as [<-|Hne]; [rewrite Hb; reflexivity | apply andb_false_r].
- rewrite Z.bits_0. destruct (Z.eqb_spec 4 i) as [<-|Hne]; [rewrite Hb; reflexivity | apply andb_false_r].
Qed.
Lemma hbp_k_neg : forall z, - 2 ^ 64 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2 ^ 64.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
symmetry. apply (Z.mod_unique z (2 ^ 64) (-1)); lia.
Qed.

Section h. Context {fx : YK11.FPState}.
Lemma hbp_k_soff : forall E n c v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v Hn. cbn [sv_denot]. rewrite Hn. reflexivity. Qed.
Lemma hbp_k_and_lit : forall E n x k, bv_unsigned (ew E n) = x -> 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 63 ->
sv_denot E (SAlu ALU_AND (SOff n 0) (SLit k)) = Z_to_bv 64 (Z.land x k).
Proof.
intros E n x k Hn Hx Hk. cbn [sv_denot]. rewrite Hn, Z.add_0_r, and_lit_Z. f_equal.
unfold YP0m.zsigned64, zcanon, M64. rewrite !Z.mod_small by lia.
destruct (Z.ltb_spec k (2 ^ 63)); [reflexivity | lia].
Qed.
Lemma hbp_k_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l IH]; cbn in *; [exact H2 | tauto]. Qed.
Lemma hbp_k_alias_app : forall E l1 l2, alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[a b] l IH]; cbn in *; [exact H2 | tauto]. Qed.

(* ---- reading the end state: an 8-byte cell, and the single bytes a run stored ---- *)
Definition hbp_k_find (n : nat) (rs : smem) (o : Z) : option sv :=
match List.find (fun r => match YP09.r_base r with Some m => Nat.eqb m n | None => false end &&
  existsb (fun c => (YP09.c_off c =? o) && match YP09.c_val c with CVal w _ => N.eqb w 8 | _ => false end) (YP09.r_chunks r)) rs with
| Some r =>
  match List.find (fun c => (YP09.c_off c =? o) && match YP09.c_val c with CVal w _ => N.eqb w 8 | _ => false end) (YP09.r_chunks r) with
  | Some c => match YP09.c_val c with CVal _ v => Some v | _ => None end
  | None => None
  end
| None => None
end.
Lemma hbp_k_slot : forall E ss ms (H : word -> bool) n b o e v,
st_ok rsegs E ss (restrict H ms) -> hbp_k_find n (ss_mem ss) o = Some e -> bv_unsigned (ew E n) = b ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem rsegs (mrestrict H (ms_mem ms)) (b + o) 8 v.
Proof.
intros E ss ms H n b o e v HS Hf Hn He Hv. unfold hbp_k_find in Hf.
destruct (List.find _ (ss_mem ss)) as [r|] eqn:Hr; [|discriminate].
apply find_some in Hr as [Hr Hq]. apply andb_prop in Hq as [Hbase _].
destruct (YP09.r_base r) as [m|] eqn:Hrb; [|discriminate]. apply Nat.eqb_eq in Hbase. subst m.
destruct (List.find _ (YP09.r_chunks r)) as [c|] eqn:Hc; [|discriminate].
apply find_some in Hc as [Hc Hq]. apply andb_prop in Hq as [Ho Hw]. apply Z.eqb_eq in Ho.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in *. subst co.
destruct cv as [w e'| | | ]; try discriminate. apply N.eqb_eq in Hw. subst w. injection Hf as Hf. subst e'.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite Hrb in Hck. cbn [base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E _ b o 8 e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Definition hbp_k_bytes_b (n : nat) (rs : smem) (l : list Z) : bool :=
forallb (fun j => (0 <=? nth j l 0) && (nth j l 0 <? 256) &&
  existsb (fun r => match YP09.r_base r with Some m => Nat.eqb m n | None => false end &&
    existsb (fun c => (YP09.c_off c =? Z.of_nat j) &&
      match YP09.c_val c with CVal w (SLit z) => N.eqb w 1 && (z mod 256 =? nth j l 0) | _ => false end)
    (YP09.r_chunks r)) rs) (seq 0 (length l)).
Lemma hbp_k_bytes : forall E ss ms (H : word -> bool) n b l,
st_ok rsegs E ss (restrict H ms) -> hbp_k_bytes_b n (ss_mem ss) l = true -> bv_unsigned (ew E n) = b ->
garr8 rsegs (mrestrict H (ms_mem ms)) b l.
Proof.
intros E ss ms H n b l HS Hb Hn j Hj.
assert (Hjs : In j (seq 0 (length l))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hb j Hjs) as Hq. cbn beta in Hq.
apply andb_prop in Hq as [Hq Hex]. apply andb_prop in Hq as [H0 H256]. apply Z.leb_le in H0. apply Z.ltb_lt in H256.
split; [|lia].
apply existsb_exists in Hex as (r & Hr & Hq). apply andb_prop in Hq as [Hbase Hc].
destruct (YP09.r_base r) as [m|] eqn:Hrb; [|discriminate]. apply Nat.eqb_eq in Hbase. subst m.
apply existsb_exists in Hc as (c & Hc & Hq). apply andb_prop in Hq as [Ho Hw].
apply Z.eqb_eq in Ho. destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in *. subst co.
destruct cv as [w [z| | | | | | | | | | ]| | | ]; try discriminate.
apply andb_prop in Hw as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst w.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite Hrb in Hck. cbn [base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bt & Hcb & Hmb). cbn [cbyte YP09.c_val] in Hcb. injection Hcb as <-.
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [YP09.c_off] in Hmb. change (Z.of_nat 0) with 0.
rewrite Z.add_0_r. rewrite Z.add_0_r in Hmb. change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in Hmb.
rewrite Hmb. f_equal.
rewrite hm_le_byte_1 by lia. apply bv_eq. unfold byte_of_word. cbn [sv_denot]. change (8 * 0) with 0.
rewrite Z.shiftr_0_r. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_modulus 8) with 256. rewrite <- Hz. rewrite Z.mod_mod by lia.
rewrite (Z.div_mod z (2 ^ 64)) at 2 by lia. rewrite Z.add_comm.
replace (2 ^ 64 * (z / 2 ^ 64)) with ((2 ^ 56 * (z / 2 ^ 64)) * 256) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.
End h.

(* ---- the env's values ---- *)
Lemma hbp_k_env : forall (regs : bvmap 5 word) R pp plen sel seen,
getr regs 9 = w64 R -> getr regs 11 = w64 sel -> getr regs 20 = w64 seen -> getr regs 27 = w64 SHADOW_OFF ->
0 <= R < 2 ^ 64 -> 4096 <= pp -> pp + 19744 < 2 ^ 64 -> 0 <= plen <= 5424 -> 0 <= sel < 256 -> 0 <= seen <= 1 ->
let E := Ereg regs (hbp_extra (hbp_k_x pp plen sel)) in
bv_unsigned (ew E 9) = R /\ bv_unsigned (ew E 11) = sel /\ bv_unsigned (ew E 20) = seen /\
bv_unsigned (ew E 27) = SHADOW_OFF /\
bv_unsigned (ew E 33) = pp /\ bv_unsigned (ew E 34) = plen /\ bv_unsigned (ew E 35) = 2 ^ 64 - pp - 1 /\
bv_unsigned (ew E 36) = pp + plen /\ bv_unsigned (ew E 37) = sel mod 4 /\
bv_unsigned (ew E 38) = plen - 16381 + 2 ^ 64 /\ bv_unsigned (ew E 39) = plen - 16377 + 2 ^ 64.
Proof.
intros regs R pp plen sel seen H9 H11 H20 H27 HR Hpp0 Hpp1 Hp Hs Hn E. subst E.
repeat match goal with |- _ /\ _ => split end.
- rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia.
- change (ew (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) 33) with (Z_to_bv 64 pp).
  apply unsigned_lit_small. lia.
- change (ew (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) 34) with (Z_to_bv 64 plen).
  apply unsigned_lit_small. lia.
- change (ew (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) 35) with (Z_to_bv 64 (- pp - 1)).
  rewrite hbp_k_neg by lia. lia.
- change (ew (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) 36) with (Z_to_bv 64 (pp + plen)).
  apply unsigned_lit_small. lia.
- change (ew (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) 37) with (Z_to_bv 64 (sel mod 4)).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound sel 4 ltac:(lia)). lia.
- change (ew (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) 38) with (Z_to_bv 64 (plen - 16381)).
  rewrite hbp_k_neg by lia. reflexivity.
- change (ew (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) 39) with (Z_to_bv 64 (plen - 16377)).
  rewrite hbp_k_neg by lia. reflexivity.
Qed.

(* ---- the walk's plumbing for this block ---- *)
(* the write rights: the cell R+0x140 lies in the caller's stack window; pp's block was made since the journal's
   start (HPgBase.hd_fresh_awr) *)
Ltac hbp_k_awr_stk := idtac; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; lia.
Ltac hbp_k_awr_pp := idtac; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
lazymatch goal with Hin : In (?p, Layout.PP_SIZE) _, Hout : ~ In (?p, Layout.PP_SIZE) _ |- _ =>
replace a with (p + (a - p)) by lia;
apply (hd_fresh_awr _ _ _ _ _ _ _ p Layout.PP_SIZE); [exact Hin | exact Hout | change (req_size Layout.PP_SIZE) with 19744; lia]
end.
Ltac hbp_k_awr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | eassumption | hbp_k_awr_stk | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat); [reflexivity | eassumption | hbp_k_awr_pp | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 36%nat); [reflexivity | eassumption | hbp_k_awr_pp | ] ].
(* every write window of the run lies in the block's write set *)
Ltac hbp_k_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
   lazymatch goal with U9 : bv_unsigned (ew _ 9) = _, U33 : bv_unsigned (ew _ 33) = _,
     U36 : bv_unsigned (ew _ 36) = _ |- _ => rewrite ?U9, ?U33, ?U36 in Hb end; lia | ]);
destruct Hr.
Ltac hbp_k_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok hbp_tbl_ok HS HJ SHOK HBPspan stop; [hbp_k_awr | ] end.
(* the value of an 8-byte cell / the single bytes of a region at the end of the run *)
Ltac hbp_k_val := first [ reflexivity | (erewrite hbp_k_soff by eassumption; f_equal; lia) ].
Ltac hbp_k_slot_tac n b o Ub :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
let r := eval vm_compute in (hbp_k_find n (ss_mem ss) o) in
lazymatch r with Some ?e =>
apply (hbp_k_slot E ss ms H n b o e); [exact HS | vm_compute; reflexivity | exact Ub | hbp_k_val | lia]
end end.
Ltac hbp_k_bytes_tac n b Ub :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
apply (hbp_k_bytes E ss ms H n b); [exact HS | vm_compute; reflexivity | exact Ub]
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the entry state holds at 0x81590 *)
Lemma hbp_k_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R pp plen sel seen (z3 b4 : bool),
getr regs 9 = w64 R -> getr regs 11 = w64 sel -> getr regs 20 = w64 seen -> getr regs 27 = w64 SHADOW_OFF ->
70368744177664 <= R -> R + 0x158 <= 140737488355328 -> R mod 16 = 0 ->
pp mod 16 = 0 -> 4096 <= pp -> pp <= HBP_PPHI -> pp + 19744 <= R ->
(forall o, 0x140 <= o < 0x148 -> apresent (w_H W) memc (R + o)) ->
(forall o, 0 <= o < 19744 -> apresent (w_H W) memc (pp + o)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x70) 8 0x10003 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 HBP_M4001 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 0x80001 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 HBP_M3FFD ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen ->
0 <= plen <= 5424 -> 0 <= sel < 256 -> 0 <= seen <= 1 ->
(sel mod 4 =? 0) = z3 -> Z.testbit sel 4 = b4 ->
st_ok rsegs (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) (hbp_k_ss z3 b4 seen)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HBP_SELK) memc (seg_rom rsegs))).
Proof.
intros W regs memc R pp plen sel seen z3 b4 H9 H11 H20 H27 HR0 HR1 HR16 Hpp16 Hpp0 Hpp1 HppR HpR Hppp
  V70 Va8 Vb0 Vf0 V108 V138 V148 V150 Vlen Hp Hs Hn Hz3 Hb4.
unfold HBP_PPHI in Hpp1.
destruct (hbp_k_env regs R pp plen sel seen H9 H11 H20 H27 ltac:(lia) ltac:(lia) ltac:(lia)
  Hp Hs Hn) as (U9 & U11 & U20 & U27 & U33 & U34 & U35 & U36 & U37 & U38 & U39).
set (E := Ereg regs (hbp_extra (hbp_k_x pp plen sel))) in *.
assert (Hnp : ((- pp - 1) mod 2 ^ 64) = 2 ^ 64 - pp - 1).
{ rewrite <- (Z.mod_add (- pp - 1) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
rewrite Hnp in Vf0.
unfold hbp_k_ss. rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- change (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) with E. clearbody E.
  repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok, hbp_k_slot_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply HpR; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * eapply hbp_chunk8; [reflexivity | lia | exact V70].
    * eapply hbp_chunk8; [reflexivity | unfold HBP_M4001; lia | exact Va8].
    * eapply hbp_chunk8; [reflexivity | lia | exact Vb0].
    * eapply hbp_chunk8; [ | | exact Vf0].
      -- cbn [sv_denot]. rewrite U35, Z.add_0_r. reflexivity.
      -- lia.
    * eapply hbp_chunk8; [reflexivity | unfold HBP_M3FFD; lia | exact V108].
    * eapply hbp_chunk8; [ | | exact V138].
      -- cbn [sv_denot]. rewrite U33. reflexivity.
      -- lia.
    * eapply hbp_chunk8; [ | | exact V148].
      -- cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
      -- lia.
    * eapply hbp_chunk8; [ | | exact V150].
      -- unfold hbp_k_shx. rewrite denot_lit_U. apply Z_to_bv64_eq_mod.
         rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, !U_SOff, U33, U27, !Z.add_0_r.
         change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
         rewrite (Z.mod_small (pp + 0x4000)) by lia.
         rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
         rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
         assert (0 <= (pp + 0x4000) / 8 < 2 ^ 61)
           by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
         rewrite (Z.mod_small ((pp + 0x4000) / 8)) by lia.
         rewrite (Z.mod_small ((pp + 0x4000) / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
         unfold shadow_addr. rewrite Z.mod_mod by lia. f_equal. lia.
      -- pose proof (Z.mod_pos_bound (shadow_addr (pp + 0x4000)) (2 ^ 64) ltac:(lia)). lia.
  + unfold region_ok, hbp_k_len_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Hppp; lia|].
    apply Forall_cons; [|apply Forall_nil].
    eapply hbp_chunk8; [ | | exact Vlen];
      [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | lia].
  + unfold region_ok, hbp_k_buf_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U36. split; [lia|]. split; [lia|].
    split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable rsegs).
    replace (pp + plen + o) with (pp + (plen + o)) by lia. apply Hppp. lia.
- change (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) with E. clearbody E.
  apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val hbp_k_slot_r hbp_k_len_r hbp_k_buf_r].
  rewrite U9, U33, U36. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- change (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) with E. clearbody E.
  unfold hbp_k_facts, facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I|]].
  + apply hbp_k_atoms_app.
    * unfold hbp_k_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U11, U20, U27, U33, U34, U35, U36, U38, U39.
      repeat match goal with |- _ /\ _ => split | |- True => exact I end;
      first [ (change (2 ^ 0) with 1; apply Z.mod_1_r) | (change (2 ^ 4) with 16; assumption)
            | (unfold SHADOW_OFF; lia) | (unfold HBP_PPHI; lia) | lia ].
    * destruct z3; cbn [hbp_k_ex atoms_ok]; [exact I|]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U37. apply Z.eqb_neq in Hz3.
      pose proof (Z.mod_pos_bound sel 4 ltac:(lia)).
      split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
  + apply hbp_k_alias_app.
    * unfold hbp_k_al0. cbn [alias_ok]. repeat split.
      -- apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 33 0) (SOff 34 0))))
           with (U E (SAlu ALU_ADD (SOff 33 0) (SOff 34 0))).
         rewrite U_add_off_atom by (rewrite ?U33, ?U34; unfold M64; lia).
         rewrite U33, U34. rewrite (hbp_k_soff E 36 0 (pp + plen) U36).
         rewrite unsigned_lit_small by lia. lia.
      -- apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 33 0) (SOff 34 4))))
           with (U E (SAlu ALU_ADD (SOff 33 0) (SOff 34 4))).
         rewrite U_add_off_atom by (rewrite ?U33, ?U34; unfold M64; lia).
         rewrite U33, U34. rewrite (hbp_k_soff E 36 4 (pp + plen) U36).
         rewrite unsigned_lit_small by lia. lia.
      -- rewrite (hbp_k_soff E 34 (-16381) plen U34), (hbp_k_soff E 38 0 _ U38). apply bv_eq.
         rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r.
         replace (plen - 16381 + 2 ^ 64) with ((plen + -16381) + 1 * 2 ^ 64) by ring.
         rewrite Z.mod_add by lia. reflexivity.
      -- rewrite (hbp_k_soff E 34 (-16377) plen U34), (hbp_k_soff E 39 0 _ U39). apply bv_eq.
         rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r.
         replace (plen - 16377 + 2 ^ 64) with ((plen + -16377) + 1 * 2 ^ 64) by ring.
         rewrite Z.mod_add by lia. reflexivity.
    * destruct z3, b4; cbn [hbp_k_al alias_ok]; (split; [|split; [|exact I]]);
      (rewrite (hbp_k_and_lit E 11 sel _ U11) by lia);
      first [ (rewrite hbp_k_land16, Hb4; reflexivity)
            | (rewrite hbp_k_land3; first [ (apply Z.eqb_eq in Hz3; rewrite Hz3; reflexivity)
                                          | (rewrite (hbp_k_soff E 37 0 _ U37), Z.add_0_r; reflexivity) ]) ].
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the shadow entries: pp's whole block and the 16 bytes from pp + len are addressable, outside the band *)
Lemma hbp_k_shok : forall ly S W mem md E pp plen,
AR rsegs B ly S W mem md -> In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
bv_unsigned (ew E 27) = SHADOW_OFF -> bv_unsigned (ew E 33) = pp -> bv_unsigned (ew E 36) = pp + plen ->
0 <= plen -> plen + 16 <= 19744 -> 4096 <= pp -> pp + 19744 <= 140737479966720 -> in_app pp 19744 ->
sh_ok rsegs hbp_k_Bx hbp_k_SH E (mrestrict (w_H W) mem).
Proof using LAWS.
intros ly S W mem md E pp plen HAR Hin U27 U33 U36 Hp0 Hp1 Hpp0 Hpp1 Happ.
assert (UB : U E hbp_k_Bx = SHADOW_OFF)
  by (unfold hbp_k_Bx; rewrite U_SOff, U27, Z.add_0_r; apply zcanon_id; unfold SHADOW_OFF, M64; lia).
assert (HAP : forall a, pp <= a < pp + 19744 -> ~ (U E hbp_k_Bx <= a < U E hbp_k_Bx + 17592186044416)).
{ intros a Ha. rewrite UB. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (V33 : U E (SOff 33 0) = pp) by (rewrite U_SOff, U33, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (V36 : U E (SOff 36 0) = pp + plen) by (rewrite U_SOff, U36, Z.add_0_r; apply zcanon_id; unfold M64; lia).
unfold sh_ok, hbp_k_SH. constructor; [|constructor; [|constructor]]; split; cbn [she_m she_lo she_hi].
- rewrite V33. eapply (obl_of_block rsegs B LAWS); [exact HAR | exact Hin | exact UB | lia |
    change (req_size Layout.PP_SIZE) with 19744; lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite V33 in Ha. apply HAP. lia.
- rewrite V36. eapply (obl_of_block rsegs B LAWS); [exact HAR | exact Hin | exact UB | lia |
    change (req_size Layout.PP_SIZE) with 19744; lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite V36 in Ha. apply HAP. lia.
Qed.

(* ---- the block SELK 0x81590 -> SELS 0x816fc (params Struct) / SELI 0x828ec (Int pod) ---- *)
Definition hbp_key_R (R pp plen sel seen : Z)
(W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
getr regs2 14 = w64 (if sel mod 4 =? 0 then seen else 1) /\
getr regs2 6 = w64 (-0x4001) /\ getr regs2 18 = w64 (pp + 0x4000) /\
garr8 rsegs (mrestrict (w_H W2) mem2) (pp + plen)
  (map (fun x : byte => bv_unsigned x)
       (le32 (if sel mod 4 =? 0 then 0x10003 else 0x80001) ++ le32 0)) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (plen + 8) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x140) 8 (if sel mod 4 =? 0 then 0 else 1 - seen).

Lemma hbp_key : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp plen sel seen : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 11 = w64 sel -> getr regs 20 = w64 seen -> getr regs 27 = w64 SHADOW_OFF ->
sp0 - STK + T_SEG_STK <= R -> R + 0x220 <= sp0 -> R mod 16 = 0 ->
70368744177664 <= R -> sp0 <= 140737488355328 -> alloc_ceiling + T_SEG_STK <= R ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x70) 8 0x10003 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 HBP_M4001 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 0x80001 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 HBP_M3FFD ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen ->
0 <= plen -> plen + 16 <= 5440 -> 0 <= sel < 256 -> (seen = 0 \/ seen = 1) ->
SRr rsegs W (cfg_at rsegs HBP_SELK regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
 (if (sel mod 4 =? 0) || Z.testbit sel 4 then HBP_SELI else HBP_SELS)
 [6; 10; 11; 12; 13; 14; 15; 16; 18]%bv
 (fun a => pp + plen <= a < pp + plen + 8 \/ pp + 0x4000 <= a < pp + 0x4008 \/ R + 0x140 <= a < R + 0x148)
 (hbp_key_R R pp plen sel seen)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp plen sel seen HJ H9 H11 H20 H27
  HRlo HRhi HR16 HR46 HS47 HRc Hin Hout V70 Va8 Vb0 Vf0 V108 V138 V148 V150 Vlen Hp0 Hp16 Hsel Hseen.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof YM05.alloc_ceiling_val as (ACV & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hpp16 & Hpp4k & Hppc & Happ & Hppres & _).
change (req_size Layout.PP_SIZE) with 19744 in Hppc, Happ, Hppres.
unfold T_SEG_STK, ASTACK in HRlo, HRc.
assert (HpR : forall o, 0x140 <= o < 0x148 -> apresent (w_H W) memc (R + o)) by (intros o Ho; apply Hpres; lia).
assert (Hppp : forall o, 0 <= o < 19744 -> apresent (w_H W) memc (pp + o))
  by (intros o Ho; apply (Hppres (pp + o)); lia).
assert (HppHI : pp <= HBP_PPHI) by (unfold HBP_PPHI; lia).
assert (HppR : pp + 19744 <= R) by lia.
assert (Hppc' : pp + 19744 <= 140737479966720) by lia.
destruct (sel mod 4 =? 0) eqn:Hz3; destruct (Z.testbit sel 4) eqn:Hb4; destruct Hseen as [Hs | Hs]; subst seen;
cbv beta iota delta [orb].
all: pose proof (hbp_k_entry W regs memc R pp plen sel _ _ _ H9 H11 H20 H27 HR46 ltac:(lia) HR16
  Hpp16 Hpp4k HppHI HppR HpR Hppp V70 Va8 Vb0 Vf0 V108 V138 V148 V150 Vlen ltac:(lia) Hsel ltac:(lia) Hz3 Hb4)
  as HS.
all: destruct (hbp_k_env regs R pp plen sel _ H9 H11 H20 H27 ltac:(lia) Hpp4k ltac:(lia)
  ltac:(lia) Hsel ltac:(lia)) as (U9 & U11 & U20 & U27 & U33 & U34 & U35 & U36 & U37 & U38 & U39).
all: pose proof (hbp_k_shok lyc Sc W memc mdc (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) pp plen
  HAR Hin U27 U33 U36 ltac:(lia) ltac:(lia) Hpp4k Hppc' Happ) as SHOK.
all: remember (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) as E eqn:HE.
all: assert (HAE : env_agree 32 (Ereg regs (hbp_extra (hbp_k_x pp plen sel))) E)
  by (subst E; apply env_agree_refl).
all: clear HE.
all: assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ (pp + plen <= a < pp + plen + 8 \/ pp + 0x4000 <= a < pp + 0x4008 \/ R + 0x140 <= a < R + 0x148) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
all: unfold cfg_at; change (w64 HBP_SELK) with (Z_to_bv 64 HBP_SELK).
all: lazymatch goal with |- context [hdu_blk_postE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pc _ _ _] => hbp_k_run pc end.
all: hbp_keep hbp_k_kwr.
all: hbp_leaf (hbp_extra (hbp_k_x pp plen sel)).
all: unfold hbp_key_R.
all: rewrite ?Hz3.
all: cbv beta iota.
all: split; [hbp_reg (14%bv : bv 5);
     first [ (cbn [sv_denot]; unfold w64; reflexivity)
           | (rewrite (hbp_k_soff _ 20 0 _ U20); unfold w64; f_equal; lia) ]|].
all: split; [hbp_reg (6%bv : bv 5); cbn [sv_denot]; unfold w64; apply Z_to_bv64_eq_mod;
     vm_compute; reflexivity|].
all: split; [hbp_reg (18%bv : bv 5); rewrite (hbp_k_soff _ 33 _ pp U33); unfold w64; f_equal; lia|].
all: split; [hbp_k_bytes_tac 36%nat (pp + plen) U36|].
all: split; [hbp_k_slot_tac 33%nat pp 16384 U33|].
all: hbp_k_slot_tac 9%nat R 320 U9.
Qed.

(* ================================ the piece: SELK -> SELS / SELI ================================ *)
Lemma hbp_piece_key : hsu_piece_W4_key_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using MTL LAWS.
unfold hsu_piece_W4_key_stmt. intros cx POST rest i Hst HSS HSI.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (hbp_R_bounds B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (hbp_blk_bounds B LAWS cx _ Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (hbp_pp_blocks B LAWS cx _ Hpre) as (Ppin & Ppout & PA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof YM05.alloc_ceiling_val as (ACV & _).
unfold hsu_from_SELK. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hselr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hpsl & Hsh & Hnp & Hps & Hnp3).
pose proof Hcore as (HJ & _ & _ & HPerm & _).
assert (Ppin2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
destruct (hbp_img_bounds sh ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
unfold hsu_at_cx in Hat.
hbp_take Hat (LReg 9) (e_R (x_e cx)) A9.
hbp_take Hat (LReg 11) sel A11.
hbp_take Hat (LReg 20) (hsu_seen ps) A20.
hbp_take Hat (LReg 27) SHADOW_OFF A27.
hbp_take Hat (LCell XR 0x70) 0x10003 A70.
hbp_take Hat (LCell XR 0xa8) (-0x4001) Aa8.
hbp_take Hat (LCell XR 0xb0) 0x80001 Ab0.
hbp_take Hat (LCell XR 0xf0) (- e_pp (x_e cx) - 1) Af0.
hbp_take Hat (LCell XR 0x108) (-0x3ffd) A108.
hbp_take Hat (LCell XR 0x138) (e_pp (x_e cx) + 0x4000) A138.
hbp_take Hat (LCell XR 0x148) (e_pp (x_e cx)) A148.
hbp_take Hat (LCell XR 0x150) (shadow_addr (e_pp (x_e cx) + 0x4000)) A150.
assert (M1 : (-0x4001) mod 2 ^ 64 = HBP_M4001) by reflexivity.
assert (M2 : (-0x3ffd) mod 2 ^ 64 = HBP_M3FFD) by reflexivity.
rewrite M1 in Aa8. rewrite M2 in A108.
rewrite Z.mod_small in A70, Ab0 by lia.
rewrite Z.mod_small in A138 by (unfold Layout.PP_SIZE in *; lia).
rewrite Z.mod_small in A148 by (unfold Layout.PP_SIZE in *; lia).
assert (Hseen : hsu_seen ps = 0 \/ hsu_seen ps = 1)
  by (unfold hsu_seen; destruct (existsb _ _); cbn; lia).
assert (Hfirst : hsu_first ps = 1 - hsu_seen ps)
  by (unfold hsu_first, hsu_seen; destruct (existsb _ _); reflexivity).
assert (Hplen : hsu_plen sh ps = Z.of_nat (length (pc_buf (PbCut sh ps None)))) by reflexivity.
assert (HplenA : 0 <= hsu_plen sh ps) by (unfold hsu_plen; lia).
assert (HplenC : hsu_plen sh ps + 16 <= 5440) by (unfold hsu_plen; exact IB1).
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (hsu_plen sh ps)).
{ rewrite Hplen. unfold hsu_pp_at, pc_image in Hpp.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut sh ps None))) <= Layout.POD_BUF_MAX)
    by (unfold Layout.POD_BUF_MAX; lia).
  change 0x4000 with Layout.OFF_LEN.
  exact (hm_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
eapply SRr_bind.
{ refine (hbp_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_pp (x_e cx))
    (hsu_plen sh ps) sel (hsu_seen ps)
    HJ A9 A11 A20 A27 RB1 RB2 RB3 _ _ RB7 Ppin2 Ppout A70 Aa8 Ab0 Af0 A108 A138 A148 A150 Alen
    HplenA HplenC Hsel Hseen); lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R14 & R6 & R18 & Rpp & Rlen & R140).
set (R := e_R (x_e cx)) in *. set (pp := e_pp (x_e cx)) in *. set (F := e_F (x_e cx)) in *.
set (plen := hsu_plen sh ps) in *.
assert (Hcore3 : hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (hbp_core_step B MT MTL cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - hbp_regs234 Hkeep.
  - intros a Ha. right. destruct Ha as [Ha|[Ha|Ha]];
    [apply hbp_E1_pp | apply hbp_E1_pp | apply hbp_E1_R];
    fold pp R; unfold Layout.PP_SIZE in *; lia. }
assert (Hfsh3 : hsu_fsh_at rsegs cx W3 mem3 (hsu_P0 headamp_himg_B)).
{ unfold hsu_fsh_at, hsu_P0 in *. eapply (hm_fsh_kept rsegs); [exact Hfsh|]. intros j Hj.
  replace (Z.of_nat (length (hi_shA headamp_himg_B))) with 116 in Hj by reflexivity. fold F.
  assert (F8 : 0 <= F / 8 <= 0xfffffff0000)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in PA.
  unfold shadow_addr, SHADOW_OFF.
  apply Hmem; [lia|]. unfold Layout.PP_SIZE in *. lia. }
assert (Hat3 : hsu_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (hsu_Rc0 rsegs cx ++ hsu_Kc rsegs cx sh np ++
   [(LReg 5, Z.of_nat (length ps)); (LReg 26, 1); (LReg 7, hsu_cur rsegs cx rest r);
    (LReg 28, Z.of_nat (length r)); (LReg 23, -8)])).
{ assert (Hat' : hsu_at rsegs (w_H W2) mem2 regs2 (x_e cx)
    (hsu_Rc0 rsegs cx ++ hsu_Kc rsegs cx sh np ++
     [(LReg 5, Z.of_nat (length ps)); (LReg 26, 1); (LReg 7, hsu_cur rsegs cx rest r);
      (LReg 28, Z.of_nat (length r)); (LReg 23, -8)])) by (hbp_list; hbp_from Hat).
  eapply hbp_at_move; [exact Hat'|].
  cbn [hsu_Rc0 hsu_Kc app]; repeat apply Forall_cons; try apply Forall_nil;
  cbn [fst hbp_kept_loc hd_xv].
  all: try (apply Hkeep; [cbv; discriminate | hbp_notin]).
  all: let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; fold R pp; apply Hmem;
    unfold T_SEG_STK, ASTACK, Layout.PP_SIZE in *; lia. }
assert (Hppk : forall kk, hm_bytes rsegs (w_H W3) mem3 (pp + plen) (le32 kk ++ le32 0) ->
  hsu_pp_at rsegs cx W3 mem3 (hsu_img_key sh ps kk)).
{ intros kk Nx. unfold hsu_pp_at, hsu_img_key. fold pp.
  unfold hsu_pp_at, pc_image in Hpp. fold pp in Hpp.
  eapply (hbp_pp_append (w_H W2) mem2 (w_H W3) mem3 pp); [| exact IB3 | exact IB4 | exact Hpp | | |].
  - rewrite length_app, !length_le32. rewrite Nat2Z.inj_add. unfold Layout.POD_BUF_MAX. lia.
  - exact Nx.
  - rewrite length_app, !length_le32, Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. unfold Layout.OFF_LEN.
    rewrite <- Hplen. fold plen. replace (plen + Z.of_nat 8) with (plen + 8) by reflexivity. exact Rlen.
  - intros y Hy Hx Hl. rewrite length_app, !length_le32 in Hx. rewrite <- Hplen in Hx. fold plen in Hx.
    apply Hmem; [unfold Layout.PP_SIZE in *; lia|].
    unfold Layout.OFF_LEN, Layout.PP_SIZE, T_SEG_STK, ASTACK in *.
    cbn [Nat.add Z.of_nat Pos.of_succ_nat] in Hx. lia. }
destruct ((sel mod 4 =? 0) || Z.testbit sel 4) eqn:Ec.
- change (mkCfg (mkst regs3 (w64 HBP_SELI) mem3 (seg_rom rsegs)) md3)
    with (cfg_at rsegs (bi_SELI headamp_bld_B) regs3 mem3 md3).
  apply (HSI ly3 S3 W3 regs3 mem3 md3 sh np sel ps r Hlen).
  split.
  + split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hin|]. split; [exact Hsuf|].
    split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hpsl|]. split; [exact Hsh|].
    split; [exact Hnp|]. split; [exact Hps | exact Hnp3].
  + split.
    * hbp_list; first [hbp_from Hat3 | idtac].
      -- cbn [hd_at]. exact R14.
      -- cbn [hd_at hd_xv]. fold R. rewrite Hfirst.
         rewrite Z.mod_small
           by (destruct Hseen as [E1|E1]; rewrite E1; destruct (sel mod 4 =? 0); lia).
         exact R140.
    * split; [apply Hppk; unfold hsu_key_of, hm_bytes; exact Rpp|].
      split; [exact Hsh7|]. split; [exact Hsel|]. split; [|exact Hselr].
      apply orb_true_iff in Ec as [E|E]; [left; apply Z.eqb_eq; exact E | right; exact E].
- change (mkCfg (mkst regs3 (w64 HBP_SELS) mem3 (seg_rom rsegs)) md3)
    with (cfg_at rsegs (bi_SELS headamp_bld_B) regs3 mem3 md3).
  apply orb_false_iff in Ec as [Ez E4]. pose proof Ez as E0. apply Z.eqb_neq in E0.
  rewrite Ez in Rpp.
  apply (HSS ly3 S3 W3 regs3 mem3 md3 sh np sel ps r Hlen).
  split.
  + split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hin|]. split; [exact Hsuf|].
    split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hpsl|]. split; [exact Hsh|].
    split; [exact Hnp|]. split; [exact Hps | exact Hnp3].
  + split.
    * hbp_list; first [hbp_from Hat3 | idtac].
      -- cbn [hd_at]. exact R14.
      -- cbn [hd_at hd_xv]. fold R. rewrite Hfirst.
         rewrite Z.mod_small
           by (destruct Hseen as [E1|E1]; rewrite E1; destruct (sel mod 4 =? 0); lia).
         exact R140.
      -- cbn [hd_at]. exact R6.
      -- cbn [hd_at]. exact R18.
    * split; [apply Hppk; unfold hm_bytes; exact Rpp|].
      split; [exact Hsh7|]. split; [exact Hsel|]. split; [exact E0|]. split; [exact E4 | exact Hselr].
Qed.

End d.
End b.

Print Assumptions hbp_key.
Print Assumptions hbp_piece_key.
