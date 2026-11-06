(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v, with its module names changed; 584 of its 659 lines of code are new or changed and 424 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v, with its module paths, module names, addresses and numbers changed; 89 of its 612 lines of code are new or changed and 136 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 164759458cd; module paths changed, rm_ -> hm_, rl_ -> hd_, every pc moved to image A of fuzz_headamp (start 0x82808, the memset entry 0x521a8, return address 0x82998, end 0x82ac0), the real-frame cells moved to headamp's (at R+0xc0, first R+0xe8, pp + 0x400c R+0x78, the capacity bounds R+0x100 / R+0x108), pp read from the cell R+0xf0 as its own atom where role keeps it in s11, the call taken through HPgIntrin.hd_memset_at in place of role's w5i_memset_at, the AR_laws Section hypothesis replaced by the kernel theorem YG0q.AR_laws_ok. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses from the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the Int-7 value pod of one property, SELI
   0x82808 -> LATCH 0x82ac0, in LLVMFuzzerTestOneInput (pod.h:412-419, with pod_put32 / pod_pad of pod.h:174-192).
   Proves no function (kind: segment lemma).

   THE CODE (pc range 0x82808 .. 0x829d0 and the slow blocks 0x82bf0 .. 0x82c44)
     0x82808  ld s9,0x78(s1)   s9 = pp + 0x400c; 0x8280c-0x82810 the capacity test of the first put (not taken)
     0x82814-0x8286c  pod_put32(pp, 4) at pp + at, pp from R+0xf0 and at from R+0xc0: the checks of the first and the
                      last byte of the 4-byte store (slow blocks 0x82bf0 / 0x82bfc), four `sb`, the check of pp->len
                      (s4) and len += 4 (s5)
     0x82870-0x828e4  the check of pp->len, the capacity test, pod_put32(pp, 4) at pp + at + 4 (slow blocks 0x82c08 /
                      0x82c14)
     0x828e8-0x8295c  the check of pp->len, the capacity test, pod_put32(pp, 7) at pp + at + 8 (slow blocks 0x82c20 /
                      0x82c2c)
     0x82960-0x82990  the check of pp->len, pod_pad: s8 = (-(at + 12)) & 7 = 4, the capacity test (not taken),
                      a0 = pp + at + 12
     0x82994  jal __asan_memset (0x521a8): the four pad bytes := 0
     0x82998-0x829ac  the check of pp->len and len += s8
     0x829b0-0x829d0  the first-flag cell R + 0xe8; if set, the check of pp + 0x400c (slow block 0x82c38) and
                      has_params := 1; both arms end at 0x82ac0
   Every check of pp->len is `lbu a0,0(s4); beqz a0,8; j <report>`. Each put reloads pp from R+0xf0 (`ld a1,0xf0(s1);
   add a0,a1,a0`); s11 holds the input cursor here and the piece neither reads nor writes it.
   THE WALK. Run 1 goes from 0x82808 to the callee's entry on the kit engine (the engine steps the `jal`, so ra =
   0x82998). pp is atom 35 of the start state (the 8-byte cell R+0xf0 holds it), at is atom 34 and pp + at atom 33;
   the alias names the sum the code forms, pp + at, as atom 33. The capacity tests compare len - 0x3ffd with -0x4001
   unsigned; the start state carries the facts that the three tests after the puts are not taken as conditions (the
   engine reads len - 0x3ffd as an atom with a negative offset, whose unsigned range it does not know). The call is
   the runtime's memset contract (the Section hypothesis W5_AMEMSET), through HPgIntrin.hd_memset_at. Run 2 starts
   from a fresh state at 0x82998 and ends at 0x82ac0, once for first = 0 and once for first = 1. Every check is on
   pp's bytes, covered by shadow entries of w5_shent_blk; no error path is reached. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgMem HPgW5Kit HPgIntrin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the registers the piece may change: ra, the temporaries and the arguments (the callee), s8 and s9 *)
Definition w5i_clob : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 25; 28; 29; 30; 31]%bv.
(* atoms 32 = K, 33 = pp + atv, 34 = atv, 35 = pp *)
Definition w5i_extra (pp atv : Z) : list word := [w64 W5_SB; w64 (pp + atv); w64 atv; w64 pp].

(* ---- run 1, the start state at 0x82808; atom 10 (a0) = atv - 0x3ffd read unsigned ---- *)
Definition ih_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((20%bv : bv 5), w5_sh 35 0x4000); ((21%bv : bv 5), SOff 35 0x4000);
   ((23%bv : bv 5), w5_Bx)].
Definition ih_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x120 0 0
   [YP09.mkChunk 0xc0 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x78 (CVal 8 (SOff 35 0x400c));
    YP09.mkChunk 0xf0 (CVal 8 (SOff 35 0));
    YP09.mkChunk 0x100 (CVal 8 (SLit 18446744073709535231)); YP09.mkChunk 0x108 (CVal 8 (SLit 18446744073709535235))].
Definition ih_len : YP09.region :=
  YP09.mkRegion (Some 35%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 34 0))].
Definition ih_at : YP09.region := YP09.mkRegion (Some 33%nat) 0 12 0 12 [].
Definition ih_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (10%nat, mkAF 18446744073709535251 18446744073709540659 0);
           (32%nat, mkAF W5_SB W5_SB 0);
           (33%nat, mkAF 4096 140737479966720 3); (34%nat, mkAF 16 5424 3);
           (35%nat, mkAF 4096 140737479966720 4)]
   [mkAC BC_GEU (SOff 34 (-16377)) (SLit 18446744073709535231);
    mkAC BC_GEU (SOff 34 (-16373)) (SLit 18446744073709535231);
    mkAC BC_GEU (SOff 34 (-16369)) (SLit 18446744073709535231)]
   [(SAlu ALU_ADD (SOff 35 0) (SOff 34 0), SOff 33 0)].
Definition ss_ih : sstate := mkSS 0x82808 (w5_sr ih_ov) [ih_slots; ih_len; ih_at] None ih_facts.
Definition ih_SH : list shent := [mkSHE 35 0x4000 0x4018; mkSHE 33 0 16].

(* ---- run 2, the start state at the return address 0x82998 ---- *)
Definition it_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((20%bv : bv 5), w5_sh 35 0x4000); ((21%bv : bv 5), SOff 35 0x4000);
   ((23%bv : bv 5), w5_Bx); ((24%bv : bv 5), SLit 4); ((25%bv : bv 5), SOff 35 0x400c)].
Definition it_slots (f : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x100 0 0 [YP09.mkChunk 0xe8 (CVal 8 (SLit f))].
Definition it_len : YP09.region :=
  YP09.mkRegion (Some 35%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 34 12))].
Definition it_flag (f : Z) : YP09.region := YP09.mkRegion (Some 35%nat) 0x400c 0x4010 0x400c (0x400c + 4 * f) [].
Definition it_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (32%nat, mkAF W5_SB W5_SB 0);
           (34%nat, mkAF 16 5424 0);
           (35%nat, mkAF 4096 140737479966720 4)] [] [].
Definition ss_it (f : Z) : sstate := mkSS 0x82998 (w5_sr it_ov) [it_slots f; it_len; it_flag f] None it_facts.
Definition it_SH : list shent := [mkSHE 35 0x4000 0x4018].

(* ======================================== helpers ======================================== *)
Lemma w5i_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
(* a capacity test after a put: len + (-0x3ffd) is not below -0x4001 unsigned *)
Lemma w5i_cond : forall E (c atv : Z), bv_unsigned (ew E 34) = atv -> 16 <= atv <= 5424 ->
-16385 <= 16 + c -> c + 5424 < 0 ->
acond_ok E (mkAC BC_GEU (SOff 34 c) (SLit 18446744073709535231)).
Proof.
intros E c atv H34 Ha Hc1 Hc2. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken sv_denot].
rewrite bv_ltu_unsigned, !unsigned_lit, H34.
rewrite (w5i_zc (atv + c) (-1) (atv + c + 18446744073709551616)) by lia.
rewrite (w5i_zc 18446744073709535231 0 18446744073709535231) by lia.
apply negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma w5i_al8 : forall p a, p mod 16 = 0 -> a mod 8 = 0 -> (p + a) mod 8 = 0.
Proof.
intros p a Hp Ha.
assert (Hp8 : p mod 8 = 0).
{ rewrite (Z.div_mod p 16) by lia. rewrite Hp, Z.add_0_r.
  replace (16 * (p / 16)) with ((2 * (p / 16)) * 8) by lia. apply Z.mod_mul. lia. }
rewrite Z.add_mod by lia. rewrite Hp8, Ha. reflexivity.
Qed.
Lemma w5i_notin : forall r : bv 5, existsb (fun c => bv_eqb c r) w5i_clob = false -> ~ In r w5i_clob.
Proof.
intros r H Hin. assert (Ht : existsb (fun c => bv_eqb c r) w5i_clob = true).
{ apply existsb_exists. exists r. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
rewrite H in Ht. discriminate.
Qed.
Definition w5i_csb (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)).
Lemma w5i_csb_ok : forall z, w5i_csb z = true -> acallee_saved z.
Proof.
intros z H. unfold w5i_csb in H. unfold acallee_saved.
repeat rewrite Bool.orb_true_iff in H. rewrite Bool.andb_true_iff in H.
rewrite !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.
(* a register outside the clobber list is one the callee preserves *)
Lemma w5i_callee : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w5i_clob -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr0 Hn.
assert (HB : forallb (fun c : bv 5 => existsb (fun d => bv_eqb d c) w5i_clob || w5i_csb (bv_unsigned c))
  HPgSteps.nz_regs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB r (HPgSteps.in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply w5i_csb_ok. exact Hq.
Qed.
Lemma w5i_pres : forall (regsT regs2 : bvmap 5 word) (r : bv 5),
aregs_preserved regsT regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regsT r.
Proof. intros regsT regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* the value of a register in a final symbolic state, over atoms the run's environment keeps *)
Lemma w5i_reg_val : forall E Ef sr (regs : bvmap 5 word) (r : bv 5) v,
regs_ok Ef sr regs -> env_agree 36 E Ef -> sr_get sr r = v -> sv_atoms_lt 36 v = true ->
getr regs r = sv_denot E v.
Proof. intros E Ef sr regs r v HR HA Hv Hl. rewrite (HR r), Hv. apply (sv_denot_agree 36 E Ef v HA Hl). Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
(* the runtime's memset contract (__asan_memset at 0x521a8, HPgIntrin.A_ASAN_MEMSET) *)
Hypothesis W5_AMEMSET : aintrin_realizes rsegs B OSet 0x521a8.

(* bytes a val_mem names, carried over a memory that keeps them *)
Lemma w5i_val_kept : forall H mem H' mem' a n v,
val_mem rsegs (mrestrict H mem) a n v ->
(forall x, a <= x < a + Z.of_nat n -> aview rsegs H' mem' x = aview rsegs H mem x) ->
val_mem rsegs (mrestrict H' mem') a n v.
Proof.
intros H mem H' mem' a n v V K. apply hm_val_of_bytes. eapply hm_bytes_kept; [apply hm_bytes_of_val; exact V|].
rewrite length_Z_to_le_bytes. exact K.
Qed.
(* bytes held by one-byte chunks of a final region *)
Lemma w5i_bytes_chunks : forall E H mem base (l : list byte) cs,
Forall (YP09.chunk_ok rsegs E (mrestrict H mem) base) cs ->
(forall i, (i < length l)%nat ->
  In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (bv_unsigned (nth i l (Z_to_bv 8 0)))))) cs) ->
hm_bytes rsegs H mem base l.
Proof.
intros E H mem base l cs C Hin. rewrite Forall_forall in C. apply hm_bytes_aview. intros i Hi.
unfold aview. rewrite (w5_mbyte_chunk1 rsegs E (mrestrict H mem) base (Z.of_nat i) _ (C _ (Hin i Hi))).
cbn [option_map]. f_equal. rewrite U_SLit, hm_unsigned_byte.
pose proof (hm_byte_range (nth i l (Z_to_bv 8 0))) as Rb.
rewrite zcanon_id by (unfold M64; lia). apply Z.mod_small. exact Rb.
Qed.

(* ======================================== run 1: 0x82808 -> the callee's entry ======================================== *)
Lemma w5i_head : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R pp atv : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 10 = w64 (atv - 0x3ffd) ->
  getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 21 = w64 (pp + 0x4000) ->
  getr regs 23 = w64 SHADOW_OFF ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (pp + 0x400c) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 ((-0x4001) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 16 <= 5440 -> atv mod 8 = 0 ->
  SRr rsegs W (cfg_at rsegs 0x82808 regs memc mdc)
    (fun W2 c2 => W2 = W /\ exists regsT memT mdT,
      c2 = mkCfg (mkst regsT (Z_to_bv 64 0x521a8) memT (seg_rom rsegs)) mdT /\
      ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k /\ same_io mdc mdT /\
      (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w5i_clob -> getr regsT r = getr regs r) /\
      getr regsT 1 = w64 0x82998 /\ getr regsT 10 = w64 (pp + atv + 12) /\ getr regsT 11 = w64 0 /\
      getr regsT 12 = w64 4 /\ getr regsT 24 = w64 4 /\ getr regsT 25 = w64 (pp + 0x400c) /\
      val_mem rsegs (mrestrict (w_H W) memT) (pp + 0x4000) 8 (atv + 12) /\
      hm_bytes rsegs (w_H W) memT (pp + atv) (Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 7) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + atv <= a < pp + atv + 12) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
        aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv
  HJ Hpp Hfresh H2 H9 H10 H20 H21 H23 Vc0 V78 Vf0 V100 V108 Vlen HR16 HRlo HRhi Hat Hal Hal8.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof w5_wx as Hwx. pose proof w5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
assert (Hm1 : (-0x4001) mod 2 ^ 64 = 18446744073709535231) by reflexivity.
assert (Hm2 : (-0x3ffd) mod 2 ^ 64 = 18446744073709535235) by reflexivity.
rewrite Hm1 in V100. rewrite Hm2 in V108.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
set (E := Ereg regs (w5i_extra pp atv)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = w64 (atv - 0x3ffd)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 W5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (HE : E = Ereg regs (w5i_extra pp atv)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w5_Bx ih_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5_shent_blk B lyc Sc W memc mdc pp 19744 E 35 0x4000 0x4018 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5_shent_blk B lyc Sc W memc mdc pp 19744 E 33 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = atv + 18446744073709535235).
{ rewrite E10. unfold w64. rewrite unsigned_lit. apply (w5i_zc _ (-1)); lia. }
assert (U32 : bv_unsigned (ew E 32) = W5_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp + atv) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = pp) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5_sr ih_ov) regs).
{ apply (w5_regs_ok E regs (w5i_extra pp atv)); [exact HE|]. unfold ih_ov.
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_sh E 35 pp 0x4000 E35 E32) by lia. rewrite H20. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 35 pp 0x4000 E35) by lia. rewrite H21. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold w5_Bx. rewrite (w5_den_off E 32 W5_SB 0 E32) by (unfold W5_SB; lia).
    rewrite Z.add_0_r, H23. reflexivity. }
  apply Forall_nil. }
assert (Hal33 : (pp + atv) mod 8 = 0) by (apply w5i_al8; assumption).
assert (HFK : facts_ok E ih_facts).
{ split; [| split].
  - cbn [ih_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U10, U32, U33, U34, U35.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                        | (change (2 ^ 4) with 16; assumption) | (change (2 ^ 3) with 8; assumption) ].
  - cbn [ih_facts f_conds conds_ok].
    refine (conj _ (conj _ (conj _ I))); apply (w5i_cond E _ atv U34); lia.
  - cbn [ih_facts f_alias alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 35 pp E35), (U_atom E 34 atv E34), (U_atom E 33 (pp + atv) E33) by lia.
    apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs E ss_ih (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82808) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ih. apply (w5_entry rsegs _ _ regs (w5i_extra pp atv) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold ih_slots, ih_len, ih_at. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (hm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
      * apply (chunk_ok_val rsegs E _ R 0xc0 8 (SOff 34 0) atv);
          [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vc0 ].
      * apply (chunk_ok_val rsegs E _ R 0x78 8 (SOff 35 0x400c) (pp + 0x400c));
          [ rewrite (w5_den_off E 35 pp 0x400c E35) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V78 ].
      * apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 35 0) pp);
          [ rewrite (w5_den_off E 35 pp 0 E35) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf0 ].
      * apply (chunk_ok_val rsegs E _ R 0x100 8 (SLit 18446744073709535231) 18446744073709535231);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V100 ].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SLit 18446744073709535235) 18446744073709535235);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V108 ].
    + apply (hm_rw_region rsegs E (w_H W) memc 35 pp);
        [ exact U35 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) atv);
        [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (hm_rw_region rsegs E (w_H W) memc 33 (pp + atv));
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
  - unfold ih_slots, ih_len, ih_at; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U35, U33; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 0x82808) with (Z_to_bv 64 0x82808).
aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x521a8.
(* the write windows: pp->len and the twelve bytes at pp + atv *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 35%nat pp);
    [ reflexivity | exact U35
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (pp + atv));
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the state at the callee's entry *)
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 36 E Ef) by (first [apply env_agree_ewset2 | apply env_agree_refl]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  split; [reflexivity|];
  exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [first [apply same_io_refl | apply w5_same_io_wvb]|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (w5_regs_kept E Ef 36 (w5_sr ih_ov) (ss_regs ssf) regs (ms_regs msf) w5i_clob HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [rewrite (w5i_reg_val E Ef _ _ 1%bv (SLit 534936) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (w5i_reg_val E Ef _ _ 10%bv (SOff 33 12) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          exact (w5_den_off E 33 (pp + atv) 12 E33 ltac:(lia) ltac:(lia))|];
  split; [rewrite (w5i_reg_val E Ef _ _ 11%bv (SLit 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (w5i_reg_val E Ef _ _ 12%bv (SLit 4) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (w5i_reg_val E Ef _ _ 24%bv (SLit 4) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (w5i_reg_val E Ef _ _ 25%bv (SOff 35 0x400c) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          exact (w5_den_off E 35 pp 0x400c E35 ltac:(lia) ltac:(lia))|];
  assert (F35 : ew Ef 35 = ew E 35) by (apply (proj1 HA); lia);
  assert (F33 : ew Ef 33 = ew E 33) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rf := fresh "Rf" in let Ra := fresh "Ra" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rf HM];
  apply Forall_cons_iff in HM as [Ra _];
  let Cs := fresh "Cs" in let Cf := fresh "Cf" in let Ca := fresh "Ca" in
  destruct Rs as (_ & _ & _ & Cs); destruct Rf as (_ & _ & _ & Cf); destruct Ra as (_ & _ & _ & Ca);
  cbn [r_chunks r_base base_val] in Cs, Cf, Ca; rewrite F35, U35 in Cf; rewrite F33, U33 in Ca;
  split;
  [ apply (val_of_chunk_ok rsegs Ef _ pp 0x4000 8 (SOff 34 12) (atv + 12));
    [ rewrite Forall_forall in Cf; apply Cf; cbn [In]; repeat (first [left; reflexivity | right])
    | rewrite (sv_denot_agree 36 E Ef (SOff 34 12) HA eq_refl); exact (w5_den_off E 34 atv 12 E34 ltac:(lia) ltac:(lia))
    | change (8 * Z.of_N 8) with 64; lia | lia ]
  |];
  split;
  [ apply (w5i_bytes_chunks Ef (w_H W) (ms_mem msf) (pp + atv) _ _ Ca);
    let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
    rewrite !length_app, !length_Z_to_le_bytes in Hi;
    do 12 (destruct i as [|i]; [cbn [In]; repeat (first [left; reflexivity | right]) |]); lia
  |];
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn1 := fresh "Hn1" in let Hn2 := fresh "Hn2" in
  intros a Ha Hn1 Hn2;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply (w5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
  let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U35, ?U33 in Hb; lia | ]);
  destruct Hr
  end.
Qed.

(* ======================================== run 2: the return address 0x82998 -> 0x82ac0 ======================================== *)
Lemma w5i_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k (regs2 : bvmap 5 word) (R pp atv fsv : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs2 2 = w64 R -> getr regs2 9 = w64 R ->
  getr regs2 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs2 21 = w64 (pp + 0x4000) ->
  getr regs2 23 = w64 SHADOW_OFF -> getr regs2 24 = w64 4 -> getr regs2 25 = w64 (pp + 0x400c) ->
  val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xe8) 8 fsv ->
  val_mem rsegs (mrestrict (w_H W) mem2) (pp + 0x4000) 8 (atv + 12) ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 16 <= 5440 -> (fsv = 0 \/ fsv = 1) ->
  SRr rsegs W (mkCfg (mkst regs2 (w64 0x82998) mem2 (seg_rom rsegs)) md2)
    (fun W3 c3 => W3 = W /\ exists regs3 mem3 md3,
      c3 = mkCfg (mkst regs3 (w64 0x82ac0) mem3 (seg_rom rsegs)) md3 /\
      ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k /\ same_io md2 md3 /\
      (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w5i_clob -> getr regs3 r = getr regs2 r) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
        ~ (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4010) ->
        aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) mem2 a) /\
      val_mem rsegs (mrestrict (w_H W) mem3) (pp + 0x4000) 8 (atv + 16) /\
      (fsv = 1 -> hm_bytes rsegs (w_H W) mem3 (pp + 0x400c) (Z_to_le_bytes 4 1))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 R pp atv fsv
  HJ Hpp Hfresh H2 H9 H20 H21 H23 H24 H25 Vd0 Vlen HR16 HRlo HRhi Hat Hal Hfst.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof w5_wx as Hwx. pose proof w5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
set (E := Ereg regs2 (w5i_extra pp atv)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 W5_SB) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = w64 pp) by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (HE : E = Ereg regs2 (w5i_extra pp atv)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w5_Bx it_SH E (mrestrict (w_H W) mem2)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (w5_shent_blk B lyc Sc W mem2 md2 pp 19744 E 35 0x4000 0x4018 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5_SB; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = pp) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5_sr it_ov) regs2).
{ apply (w5_regs_ok E regs2 (w5i_extra pp atv)); [exact HE|]. unfold it_ov.
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_sh E 35 pp 0x4000 E35 E32) by lia. rewrite H20. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 35 pp 0x4000 E35) by lia. rewrite H21. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold w5_Bx. rewrite (w5_den_off E 32 W5_SB 0 E32) by (unfold W5_SB; lia).
    rewrite Z.add_0_r, H23. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H24. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 35 pp 0x400c E35) by lia. rewrite H25. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E it_facts).
{ split; [| split; [exact I | exact I]].
  cbn [it_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U34, U35.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                      | (change (2 ^ 4) with 16; assumption) | (change (2 ^ 3) with 8; assumption) ]. }
destruct Hfst as [-> | ->].
all: lazymatch goal with Vd : val_mem _ _ (_ + 0xe8) 8 ?f |- _ =>
  assert (HS : st_ok rsegs E (ss_it f) (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x82998) mem2 (seg_rom rsegs))));
  [ rewrite restrict_mkst_fx; unfold ss_it; apply (w5_entry rsegs _ _ regs2 (w5i_extra pp atv) E); [exact HE| | | | |];
    [ exact HR0
    | vm_compute; reflexivity
    | unfold it_slots, it_len, it_flag;
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      [ apply (hm_ro_region rsegs E (w_H W) mem2 9 R); [exact U9 | lia | lia |];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val rsegs E _ R 0xe8 8 (SLit f) f);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vd ]
      | apply (hm_rw_region rsegs E (w_H W) mem2 35 pp);
          [ exact U35 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 12) (atv + 12));
          [ rewrite (w5_den_off E 34 atv 12 E34) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ]
      | apply (hm_rw_region rsegs E (w_H W) mem2 35 pp);
          [ exact U35 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | apply Forall_nil ] ]
    | unfold it_slots, it_len, it_flag; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
      cbn [r_base r_lo r_hi base_val]; rewrite U9, U35; repeat split; try exact I; lia
    | exact HFK ]
  | ] end.
all: change (w64 0x82998) with (Z_to_bv 64 0x82998).
all: aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x82ac0.
(* the write windows: pp->len and, when first is set, has_params *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 35%nat pp);
    [ reflexivity | exact U35
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the end state at 0x82ac0 *)
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 36 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  split; [reflexivity|];
  exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [first [apply same_io_refl | apply w5_same_io_wvb]|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (w5_regs_kept E Ef 36 (w5_sr it_ov) (ss_regs ssf) regs2 (ms_regs msf) w5i_clob HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn1 := fresh "Hn1" in let Hn2 := fresh "Hn2" in
    intros a Ha Hn1 Hn2;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w5_kept_run rsegs E _ (w_H W) mem2 (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U35 in Hb;
       first [lia | (apply Hn2; split; [reflexivity | lia])] | ]);
    destruct Hr
  |];
  assert (F35 : ew Ef 35 = ew E 35) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rf := fresh "Rf" in let Rg := fresh "Rg" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rf HM];
  apply Forall_cons_iff in HM as [Rg _];
  let Cf := fresh "Cf" in let Cg := fresh "Cg" in
  destruct Rf as (_ & _ & _ & Cf); destruct Rg as (_ & _ & _ & Cg);
  cbn [r_chunks r_base base_val] in Cf, Cg; try rewrite F35 in Cf, Cg; rewrite U35 in Cf, Cg;
  rewrite Forall_forall in Cf, Cg;
  split;
  [ apply (val_of_chunk_ok rsegs Ef _ pp 0x4000 8 (SOff 34 16) (atv + 16));
    [ apply Cf; cbn [In]; repeat (first [left; reflexivity | right])
    | try rewrite (sv_denot_agree 36 E Ef (SOff 34 16) HA eq_refl); exact (w5_den_off E 34 atv 16 E34 ltac:(lia) ltac:(lia))
    | change (8 * Z.of_N 8) with 64; lia | lia ]
  |];
  let Hf1 := fresh "Hf1" in intros Hf1;
  first
  [ discriminate Hf1
  | apply hm_bytes_of_val;
    apply (val_of_chunk_ok rsegs Ef _ pp 0x400c 4 (SLit 1) 1);
    [ apply Cg; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | lia ] ]
  end.
Qed.

(* ======================================== the piece ======================================== *)
Lemma w5_int_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R pp atv fsv : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  st_nev S + k <= EV_MAX ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (atv - 0x3ffd) ->
  getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 21 = w64 (pp + 0x4000) ->
  getr regs 23 = w64 SHADOW_OFF ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 fsv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (pp + 0x400c) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 ((-0x4001) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 16 <= 5440 -> atv mod 8 = 0 -> (fsv = 0 \/ fsv = 1) ->
  SRr rsegs W (cfg_at rsegs 0x82808 regs memc mdc)
    (w5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82ac0
      [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 25; 28; 29; 30; 31]%bv
      (fun a => (pp + atv <= a < pp + atv + 16) \/ (pp + 0x4000 <= a < pp + 0x4008) \/
                (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4010))
      (fun W2 regs2 mem2 =>
        hm_bytes rsegs (w_H W2) mem2 (pp + atv)
          (Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 7 ++ repeat (Z_to_bv 8 0) 4) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 16) /\
        (fsv = 1 -> hm_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Z_to_le_bytes 4 1)))).
Proof using MTL W5_AMEMSET.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv fsv
  HJ Hpp Hfresh Hnev H2 H9 H3 H4 H10 H20 H21 H23 Vc0 Vd0 V78 Vf0 V100 V108 Vlen HR16 HRlo HRhi Hat Hal Hal8 Hfst.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil.
(* run 1 *)
eapply SRr_bind.
{ exact (w5i_head STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv HJ Hpp Hfresh
    H2 H9 H10 H20 H21 H23 Vc0 V78 Vf0 V100 V108 Vlen HR16 HRlo HRhi Hat Hal Hal8). }
intros W1 c1 _ (-> & regsT & memT & mdT & -> & HJT & HioT & HkT & T1 & T10 & T11 & T12 & T24 & T25 & VlenT & BT & KT).
rewrite HPS in Hpp, Hfresh.
assert (HART : AR rsegs B lyc Sc W memT mdT) by exact (proj1 HJT).
assert (T2 : getr regsT 2 = w64 R) by (rewrite (HkT 2%bv) by first [vm_compute; lia | apply w5i_notin; vm_compute; reflexivity]; exact H2).
assert (T3 : getr regsT 3 = w64 (as_gp B)) by (rewrite (HkT 3%bv) by first [vm_compute; lia | apply w5i_notin; vm_compute; reflexivity]; exact H3).
assert (T4 : getr regsT 4 = w64 (as_tp B)) by (rewrite (HkT 4%bv) by first [vm_compute; lia | apply w5i_notin; vm_compute; reflexivity]; exact H4).
assert (T9 : getr regsT 9 = w64 R) by (rewrite (HkT 9%bv) by first [vm_compute; lia | apply w5i_notin; vm_compute; reflexivity]; exact H9).
assert (T20 : getr regsT 20 = w64 (shadow_addr (pp + 0x4000))) by (rewrite (HkT 20%bv) by first [vm_compute; lia | apply w5i_notin; vm_compute; reflexivity]; exact H20).
assert (T21 : getr regsT 21 = w64 (pp + 0x4000)) by (rewrite (HkT 21%bv) by first [vm_compute; lia | apply w5i_notin; vm_compute; reflexivity]; exact H21).
assert (T23 : getr regsT 23 = w64 SHADOW_OFF) by (rewrite (HkT 23%bv) by first [vm_compute; lia | apply w5i_notin; vm_compute; reflexivity]; exact H23).
assert (HspT : spZ regsT = sp0 + (R - sp0)) by (unfold spZ; rewrite T2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Ho16 : (R - sp0) mod 16 = 0) by (rewrite Zminus_mod, HR16, Hsp0al; reflexivity).
(* the call *)
eapply SRr_bind.
{ refine (hd_memset_at B W5_AMEMSET W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k (pp + atv + 12) 0 4 (R - sp0)
    (w64 0x82998) HJT T10 T11 T12 _ _ _ HspT Ho16 _ _ T3 T4 T1 _ _ _ _ _).
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Hes. lia.
  - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (pp + (a - pp)) by lia.
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia].
    + rewrite Hes. lia.
  - apply (amem_range_of_block rsegs B LAWS lyc Sc W memT mdT pp 19744); [exact HART | exact Hpp | lia | cbn; lia].
  - exact (proj1 (hm_blk_ra rsegs B lyc Sc W memT mdT pp 19744 (pp + atv + 12) 4 HART Hpp ltac:(lia) ltac:(cbn; lia))).
  - exact (proj2 (hm_blk_ra rsegs B lyc Sc W memT mdT pp 19744 (pp + atv + 12) 4 HART Hpp ltac:(lia) ltac:(cbn; lia))). }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP & R10 & Z4 & K2 & _).
assert (R2 : getr regs2 2 = w64 R) by (rewrite (w5i_pres regsT regs2 2%bv HP) by (apply w5i_csb_ok; vm_compute; reflexivity); exact T2).
assert (R9 : getr regs2 9 = w64 R) by (rewrite (w5i_pres regsT regs2 9%bv HP) by (apply w5i_csb_ok; vm_compute; reflexivity); exact T9).
assert (R20 : getr regs2 20 = w64 (shadow_addr (pp + 0x4000))) by (rewrite (w5i_pres regsT regs2 20%bv HP) by (apply w5i_csb_ok; vm_compute; reflexivity); exact T20).
assert (R21 : getr regs2 21 = w64 (pp + 0x4000)) by (rewrite (w5i_pres regsT regs2 21%bv HP) by (apply w5i_csb_ok; vm_compute; reflexivity); exact T21).
assert (R23 : getr regs2 23 = w64 SHADOW_OFF) by (rewrite (w5i_pres regsT regs2 23%bv HP) by (apply w5i_csb_ok; vm_compute; reflexivity); exact T23).
assert (R24 : getr regs2 24 = w64 4) by (rewrite (w5i_pres regsT regs2 24%bv HP) by (apply w5i_csb_ok; vm_compute; reflexivity); exact T24).
assert (R25 : getr regs2 25 = w64 (pp + 0x400c)) by (rewrite (w5i_pres regsT regs2 25%bv HP) by (apply w5i_csb_ok; vm_compute; reflexivity); exact T25).
assert (Vd2 : val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xe8) 8 fsv).
{ apply (w5i_val_kept (w_H W) memc); [exact Vd0|]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  rewrite K2 by (rewrite ?Hes; lia). apply KT; lia. }
assert (Vlen2 : val_mem rsegs (mrestrict (w_H W) mem2) (pp + 0x4000) 8 (atv + 12)).
{ apply (w5i_val_kept (w_H W) memT); [exact VlenT|]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  apply K2; rewrite ?Hes; lia. }
(* run 2 *)
eapply SRr_mono.
{ exact (w5i_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 R pp atv fsv HJ2 Hpp Hfresh
    R2 R9 R20 R21 R23 R24 R25 Vd2 Vlen2 HR16 HRlo HRhi Hat Hal Hfst). }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & K3 & Vlen3 & Fl3).
assert (HspR : spZ regs = R) by (unfold spZ; rewrite H2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
unfold w5_post. exists lyc, Sc, regs3, mem3, md3.
split; [reflexivity|].
split; [exact HJ3|].
split.
{ intros r Hr0 Hr. rewrite (Hk3 r Hr0 Hr), (w5i_pres regsT regs2 r HP (w5i_callee r Hr0 Hr)). exact (HkT r Hr0 Hr). }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact (same_io_trans _ _ _ HioT (same_io_trans _ _ _ Hio2 Hio3))|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hst Hn. rewrite HspR, HTS in Hst.
  rewrite K3; [| exact Ha | intros H'; apply Hn; right; left; exact H' | intros H'; apply Hn; right; right; exact H'].
  rewrite K2; [| exact Ha | intros H'; apply Hn; left; lia | rewrite Hes; intros H'; apply Hst; lia].
  apply KT; [exact Ha | intros H'; apply Hn; left; lia | intros H'; apply Hn; right; left; exact H']. }
assert (HL : length (Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 7) = 12%nat) by reflexivity.
split; [|split; [exact Vlen3 | exact Fl3]].
replace (Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 7 ++ repeat (Z_to_bv 8 0) 4)
  with ((Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 7) ++ repeat (Z_to_bv 8 0) 4)
  by (rewrite <- !app_assoc; reflexivity).
apply hm_bytes_app. rewrite HL. split.
- eapply hm_bytes_kept; [exact BT|]. rewrite HL. intros x Hx. change (Z.of_nat 12) with 12 in Hx.
  rewrite K3 by lia. rewrite K2 by (rewrite ?Hes; lia). reflexivity.
- apply hm_bytes_aview. intros i Hi. rewrite hm_length_repeat in Hi. change (Z.of_nat 12) with 12.
  rewrite K3 by lia. rewrite Z4 by lia. rewrite hm_nth_repeat by exact Hi. reflexivity.
Qed.
End c.

Print Assumptions w5_int_core.
