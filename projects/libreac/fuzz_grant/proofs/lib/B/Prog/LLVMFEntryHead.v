(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryHead), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryHead.v. *)
(* Ported from lib/A/Prog/GrantEntryHead.v, blob 5c59cd15e8a, at a working branch 5651bf66924, whose lib/A/AB01.v is the
   current 1e6f4323d1e; the same blob byte for byte is on a working branch 7c8c67da870, a working branch 552860c6366 and
   a working branch 7d31e8f3534. *)
(* The entry segment of fuzz_grant's entry function LLVMFuzzerTestOneInput on image B (0x80a3c, the ASan + UBSan
   build): the slots 0x80a3c .. 0x80d04 (GP_entry .. GP_hdr).

   The segment takes the 288-byte machine frame (0x80a3c), saves ra and s0..s11 at sp0 - 8 .. sp0 - 104, realigns sp
   to 32 bytes (`andi sp,sp,-32` 0x80a7c; s1 := sp 0x80a80), reads the side-stack flag (1) and the shadow base
   through their GOT words (objects 0 / 36 and 1 / 35), spills the shadow base to sp1 + 144, takes the frame of class
   4 on the side stack for frames from `__asan_stack_malloc_4` (0x80ab0), writes the frame's three header words
   (0x80b14 .. 0x80b1c) and its 104 shadow bytes (GSH_entry, 0x80b2c .. 0x80cd0), and stores the frame to sp1 + 72
   (0x80d00). The two branches into the no-frame fallback (0x80aa8 on the flag, 0x80ac4 on the frame) are decided by
   the engine from the flag's constant 1 and the frame's range; the branch to the release (0x80cd4, n >> 26 <> 0) is
   refuted from n < 2 ^ 26. It ends at 0x80d04 in the state GI_hdr says. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantTop GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantPaLib YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantFrame YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1i GrantACjr ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at the first slot ---- *)
(* Atoms: 0..31 the entry registers, 32 the shadow offset, 240.. the image. The regions:
   the 288 bytes below sp, the GOT word of the shadow-base cell (object 1) and the cell
   (object 35), the GOT word of the side-stack flag (object 0) and the flag (object 36). *)
Definition GHBx : sv := SOff 32 0.
(* The shift-right of a 64-bit value by a literal, as the branch on the input's size
   at 0x80cd4 needs it. *)
Lemma gh_U_srl : forall E x k, 0 <= k < 64 -> U E (SAlu ALU_SRL x (SLit k)) = U E x / 2 ^ k.
Proof.
intros E x k Hk. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (U_range E x) as Hr. unfold M64 in *.
assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
assert (Hle : U E x / 2 ^ k <= U E x).
{ apply Z.div_le_upper_bound; [exact Hp|].
  assert (H1 : 1 <= 2 ^ k) by (rewrite <- (Z.pow_0_r 2); apply Z.pow_le_mono_r; lia).
  rewrite Z.mul_comm. rewrite <- (Z.mul_1_r (U E x)) at 1. apply Z.mul_le_mono_nonneg_l; lia. }
assert (Hge : 0 <= U E x / 2 ^ k) by (apply Z.div_pos; lia).
revert Hle Hge. generalize (U E x / 2 ^ k). intros q Hle Hge.
apply zcanon_id. unfold M64. lia.
Qed.

(* The plain engine stops at a branch it cannot decide: split on it, keeping the
   condition in the state so that the next run decides it. *)
Ltac gh_branch BR HS :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
  let r := eval vm_compute in (sym_step_pi pl_tpi ss) in
  lazymatch r with
  | PStop (SR_branch ?c ?a ?b) =>
    apply (BR W E ss ms _ _ c a b HS); clear HS;
    let Hc := fresh "Hc" in intros Hc HS
  | ?x => idtac "GH-NOT-A-BRANCH" x; fail 1 "gh_branch: the state is not stuck at a branch"
  end
| _ => fail "gh_branch: HS must be  st_ok_pi _ _ E ss (restrict (w_H W) ms)"
end.
(* The region of an atom in the engine's state, as a `region_ok` fact. *)
Ltac gh_region HS nn HR :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs nn in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict] in HR
end.


(* A byte a store left in a region's chunks, and the check that a region's chunks carry
   a whole list of bytes: the frame's 104 shadow bytes are read back this way. *)
Definition gh_cbyte (cs : list YP09.chunk) (i : Z) : option Z :=
  match find (fun c => Z.eqb (YP09.c_off c) i) cs with
  | Some c => match YP09.c_val c with
              | CVal w v => if N.eqb w 1 then match v with SLit z => Some (zcanon z mod 256) | _ => None end
                            else None
              | _ => None end
  | None => None
  end.
Definition gh_chunks_match (cs : list YP09.chunk) (sh : list Z) : bool :=
  forallb (fun i => match gh_cbyte cs (Z.of_nat i) with Some v => Z.eqb v (nth i sh 0) | None => false end)
          (seq 0 (length sh)).
(* The word a store left at an offset of a region. *)
Definition gh_cword (cs : list YP09.chunk) (i : Z) : option sv :=
  match find (fun c => Z.eqb (YP09.c_off c) i) cs with
  | Some c => match YP09.c_val c with CVal w v => if N.eqb w 8 then Some v else None | _ => None end
  | None => None
  end.


Definition GHBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gh_extra : list word := [Z_to_bv 64 SB].
Definition gh_regions0 : smem :=
  [ stack_region 288; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 36); uar_cell_regionP (A_OBJ 36) ].
Definition gh_atoms0 : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF SB SB 0) ].
Definition ss_gh0 : sstate := mkSS GP_entry sr_atoms gh_regions0 None (mkFacts gh_atoms0 [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* The bytes a region's chunks carry, read back as `aview`. *)
Lemma gh_shadow_bytes : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs sh,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  gh_chunks_match cs sh = true ->
  forall i, (i < length sh)%nat -> aview SEGS H m (base + Z.of_nat i) = Some (nth i sh 0).
Proof.
intros E H m nn base lo hi wlo whi cs sh Hr Hb Hm i Hi.
unfold gh_chunks_match in Hm. rewrite forallb_forall in Hm.
specialize (Hm i ltac:(apply in_seq; lia)).
destruct (gh_cbyte cs (Z.of_nat i)) as [v|] eqn:Hc; [|discriminate Hm].
apply Z.eqb_eq in Hm.
unfold gh_cbyte in Hc.
destruct (find (fun c => Z.eqb (YP09.c_off c) (Z.of_nat i)) cs) as [c|] eqn:Hf; [|discriminate Hc].
destruct (find_some _ _ Hf) as [Hin Hoff]. apply Z.eqb_eq in Hoff.
destruct (YP09.c_val c) as [w z| | |] eqn:Hv; try discriminate Hc.
destruct (N.eqb w 1) eqn:Hw; [|discriminate Hc]. apply N.eqb_eq in Hw. subst w.
destruct z as [zz| | | | | | | | | |]; try discriminate Hc.
injection Hc as <-.
destruct Hr as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs c Hin) as Hck.
cbn [YP09.r_base YP09.base_val] in Hck. rewrite Hb in Hck.
specialize (Hck 0 ltac:(unfold YP09.c_len; rewrite Hv; cbn [YP09.cv_len]; lia)).
destruct Hck as (b & Hcb & Hmb).
rewrite Hv in Hcb. cbn [YP09.cbyte] in Hcb. injection Hcb as <-.
rewrite Hoff, Z.add_0_r in Hmb.
unfold aview. rewrite Hmb. cbn [option_map]. f_equal. rewrite <- Hm.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
change (bv_modulus 64) with (2 ^ 64). unfold zcanon, M64. reflexivity.
Qed.

(* A word a region's chunk carries, read back as `rdword`. *)
Lemma gh_word_of_region : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs off e v,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (base + off) = Some v.
Proof.
intros E H m nn base lo hi wlo whi cs off e v Hr Hb Hin He Hv.
apply (rdword_of_val_mem SEGS H m); [|exact Hv].
change 8%nat with (N.to_nat 8).
exact (field_of_region E (mrestrict H m) nn base cs lo hi wlo whi off 8%N e v Hr Hb Hin He
  ltac:(cbn [Z.of_N]; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

(* The caller's input block, kept by a call that writes nothing in it. *)
Lemma gh_garr_keep : forall (H : word -> bool) (m m' : word -> option byte) a (l : list Z),
  (forall j, (j < length l)%nat -> aview SEGS H m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hkk. replace kk with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j) (Hk j Hj)).
pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0. exact Hv0.
Qed.
(* The same, looking the chunk up by its offset. *)
Lemma gh_word_at : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs off e v,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  gh_cword cs off = Some e ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (base + off) = Some v.
Proof.
intros E H m nn base lo hi wlo whi cs off e v Hr Hb Hc He Hv.
unfold gh_cword in Hc.
destruct (find (fun c => Z.eqb (YP09.c_off c) off) cs) as [c|] eqn:Hf; [|discriminate Hc].
destruct (find_some _ _ Hf) as [Hin Hoff]. apply Z.eqb_eq in Hoff.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hoff, Hc, Hin.
destruct cv as [w z| | |]; try discriminate Hc.
destruct (N.eqb w 8) eqn:Hw; [|discriminate Hc]. apply N.eqb_eq in Hw.
injection Hc as Hc. subst w. subst co. subst z.
exact (gh_word_of_region E H m nn base lo hi wlo whi cs off _ v Hr Hb Hin He Hv).
Qed.

(* The 13 saved words of the machine frame, read back from the region of the caller's
   stack: ra at sp - 8 and s0, s1, s2 .. s11 at sp - 16 - 8j (image B 0x80a44 .. 0x80a74). *)
Lemma gh_saved_of : forall E (H : word -> bool) (m : word -> option byte) sp0 (regs : bvmap 5 word)
  lo hi wlo whi cs,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2%nat) = sp0 ->
  (forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r) ->
  gh_cword cs (-8) = Some (SOff 1%nat 0) ->
  gh_cword cs (-16) = Some (SOff 8%nat 0) ->
  gh_cword cs (-24) = Some (SOff 9%nat 0) ->
  gh_cword cs (-32) = Some (SOff 18%nat 0) ->
  gh_cword cs (-40) = Some (SOff 19%nat 0) ->
  gh_cword cs (-48) = Some (SOff 20%nat 0) ->
  gh_cword cs (-56) = Some (SOff 21%nat 0) ->
  gh_cword cs (-64) = Some (SOff 22%nat 0) ->
  gh_cword cs (-72) = Some (SOff 23%nat 0) ->
  gh_cword cs (-80) = Some (SOff 24%nat 0) ->
  gh_cword cs (-88) = Some (SOff 25%nat 0) ->
  gh_cword cs (-96) = Some (SOff 26%nat 0) ->
  gh_cword cs (-104) = Some (SOff 27%nat 0) ->
  rdword (aview SEGS H m) (sp0 - 8) = Some (bv_unsigned (getr regs 1%bv)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS H m) (sp0 - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
Proof.
intros E H m sp0 regs lo hi wlo whi cs Hr Hb HEE K1 K8 K9 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27.
assert (W1 : forall (nn : nat) (r : bv 5) off e,
  Z.of_nat nn = bv_unsigned r -> e = SOff nn 0 -> gh_cword cs off = Some e ->
  rdword (aview SEGS H m) (sp0 + off) = Some (bv_unsigned (getr regs r))).
{ intros nn r off e Hn He Hc. subst e.
  apply (gh_word_at E H m 2%nat sp0 lo hi wlo whi cs off (SOff nn 0) _ Hr Hb Hc); [|apply u64_range].
  cbn [sv_denot]. rewrite (HEE nn r Hn), Z.add_0_r. reflexivity. }
split.
- replace (sp0 - 8) with (sp0 + -8) by lia. exact (W1 1%nat 1%bv (-8) _ eq_refl eq_refl K1).
- intros j Hj.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9
               \/ j = 10 \/ j = 11) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]]]]]];
  [ replace (sp0 - 16 - 8 * 0) with (sp0 + -16) by lia
  | replace (sp0 - 16 - 8 * 1) with (sp0 + -24) by lia
  | replace (sp0 - 16 - 8 * 2) with (sp0 + -32) by lia
  | replace (sp0 - 16 - 8 * 3) with (sp0 + -40) by lia
  | replace (sp0 - 16 - 8 * 4) with (sp0 + -48) by lia
  | replace (sp0 - 16 - 8 * 5) with (sp0 + -56) by lia
  | replace (sp0 - 16 - 8 * 6) with (sp0 + -64) by lia
  | replace (sp0 - 16 - 8 * 7) with (sp0 + -72) by lia
  | replace (sp0 - 16 - 8 * 8) with (sp0 + -80) by lia
  | replace (sp0 - 16 - 8 * 9) with (sp0 + -88) by lia
  | replace (sp0 - 16 - 8 * 10) with (sp0 + -96) by lia
  | replace (sp0 - 16 - 8 * 11) with (sp0 + -104) by lia ];
  cbn [Z.ltb Z.compare Z.add];
  [ exact (W1 8%nat (8%bv : bv 5) (-16) _ eq_refl eq_refl K8)
  | exact (W1 9%nat (9%bv : bv 5) (-24) _ eq_refl eq_refl K9)
  | exact (W1 18%nat (18%bv : bv 5) (-32) _ eq_refl eq_refl K18)
  | exact (W1 19%nat (19%bv : bv 5) (-40) _ eq_refl eq_refl K19)
  | exact (W1 20%nat (20%bv : bv 5) (-48) _ eq_refl eq_refl K20)
  | exact (W1 21%nat (21%bv : bv 5) (-56) _ eq_refl eq_refl K21)
  | exact (W1 22%nat (22%bv : bv 5) (-64) _ eq_refl eq_refl K22)
  | exact (W1 23%nat (23%bv : bv 5) (-72) _ eq_refl eq_refl K23)
  | exact (W1 24%nat (24%bv : bv 5) (-80) _ eq_refl eq_refl K24)
  | exact (W1 25%nat (25%bv : bv 5) (-88) _ eq_refl eq_refl K25)
  | exact (W1 26%nat (26%bv : bv 5) (-96) _ eq_refl eq_refl K26)
  | exact (W1 27%nat (27%bv : bv 5) (-104) _ eq_refl eq_refl K27) ].
Qed.


Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASM4 : astack_malloc_realizes SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

Lemma gh_entry : forall W ly S regs mem md n,
  afn_pre SEGS B GE_STK ly S W regs mem md [] ->
  getr regs 11 = w64 n -> 0 <= n < 2 ^ 26 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs gh_extra)) ss_gh0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GP_entry)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md n HPRE H11 Hn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : GE_STK = 32768) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TL) in Kguar.
rewrite (pal_uar_cell B TL) in Kguar, Kuar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 35 ltac:(lia)) as Hob35. pose proof (pa_obj_img 36 ltac:(lia)) as Hob36.
rewrite IMG_LO_B_val, IMG_TOP_B_val in Hob0, Hob1, Hob35, Hob36.
pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs gh_extra)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO : forall i, (i < 37)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros nn v Hn' Hv. cbn [base_val]. rewrite Hn'. apply unsigned_lit_small. exact Hv. }
unfold ss_gh0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gh_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EO 1%nat ltac:(lia))) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
    [cbn [sv_denot]; rewrite (EO 35%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbv [A_OBJ Nat.add] in *; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) (EO 35%nat ltac:(lia))) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EO 0%nat ltac:(lia))) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 36) 0) (VAL (A_OBJ 36)));
    [cbn [sv_denot]; rewrite (EO 36%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbv [A_OBJ Nat.add] in *; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + rewrite (VB (A_OBJ 36) (VAL (A_OBJ 36)) (EO 36%nat ltac:(lia))) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 36)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold gh_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EO 1%nat ltac:(lia))) by lia.
  rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) (EO 35%nat ltac:(lia))) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EO 0%nat ltac:(lia))) by lia.
  rewrite (VB (A_OBJ 36) (VAL (A_OBJ 36)) (EO 36%nat ltac:(lia))) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob35 Hob36 Hsep. clear.
  unfold zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. cbv [A_OBJ Nat.add]. intros.
  rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok gh_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E11, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hal16 Hn. clear.
  unfold SB, zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Theorem ge_head0 : forall POST,
  ge_from B MT POST (GI_hdr B) -> ge_start B MT POST.
Proof.
intros POST HM cx HB.
destruct cx as [ly S W regs mem md p pl sp1 E0 T].
pose proof HB as (HPRE & H10 & H11 & Hpn & HPL & Hfr0 & Hev & Hlive & HROD & Hsp1d & HE0 & HE02 & HE032 & HMOK & HTR & HNEED).
unfold c_n in *. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_sp1 c_E0 c_T] in *.
set (n := Z.of_nat (length pl)) in *.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn' _]]; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (gh_entry W ly S regs mem md n HPRE H11 Hn26) as HS.
pose proof (ajournal_init SEGS B GE_STK [] ly S W regs mem md [] HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : GE_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs gh_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
img_factsF E. img_hull_factsF.
rewrite IMG_LO_B_val, IMG_TOP_B_val in Hob241, Hob242, Hob276, Hob277, Huar.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs gh_extra) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros nn r Hnn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hnn).
clear HE.
change (w64 (BASE + GP_entry)) with (Z_to_bv 64 (BASE + GP_entry)).
shok_auto SHOK GHBx E (mrestrict (w_H W) mem).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
(* The saves of ra and s0..s11 and the realignment of sp (0x80a7c), up to 0x80a80. *)
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK GHBspan 0x44. { awrFL AG 0 0 EFA0. }
upd_aboveW_init HFr AG HUP. clear_frames.
(* sp is now 32 * ((sp0 - 288) / 32), c_sp1; atom 60 names it and the stack region
   below it holds the spill slots 0 .. 184 the segment writes. *)
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1d in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 (32 * ((spZ regs + -288) / 32)))
(denot_and_m32 Ev 2 (spZ regs) (-288) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(clear - Hshi H47; lia) ltac:(clear - Hceil Hslo Hstk0 FFS C1 Hshi H47; lia)) R2 end.
rewrite <- Hsp1d in R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); change (2 ^ 5) with 32;
clear - Hsp1 Hsp1al Hslo Hstk0 Hshi H47 Hceil FFS C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 184 0 184 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia|];
split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FFS; clear - Ho Hsp1; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 Hob241 Hob242 Hob276 Hob277; repeat split; zone_lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
(* The side-stack flag is read (1), the shadow base is spilled to sp1 + 144 and
   __asan_stack_malloc_4 is called at 0x80ab0. *)
hei_havoc HS; paj_run_tok RUN HS HJ SHOK GHBspan. { awrFL AG 0 0 EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm4 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 4 ASM4 ltac:(lia) W (ms_regs msX) (ms_mem msX) GE_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - clear - Hsp1; lia.
  - rewrite FFS, Hes; clear - Hsp1; lia.
  - rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hfr0. vm_compute. reflexivity. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS2 & ES2)).
rewrite Hes in HK. replace (spZ regs + (sp1 - spZ regs) - 4096) with (sp1 - 4096) in HK by (clear; lia).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; clear - Ha Hsp1 Hceil Hslo Hstk0 FFS C1; lia. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (4, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgB _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
rewrite IMG_LO_B_val, IMG_TOP_B_val in HFhigh_img.
change (fs_frame_bytes 4) with 1024 in *.
set (F := frame_addr ly 4 fpos) in *. set (FL := flag_addr ly 4 fpos) in *.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 4 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by (unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia); rewrite Z.pow_0_r, Z.mod_1_r;
  unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS;
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 1024 0 24 [YP09.mkChunk 1016 (CVal 8 (SOff 528 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 1016 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zside | zside
| replace (F + 1016) with (F + 1024 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img Hob241 Hob242 Hob276 Hob277; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 529 4 0 104 []) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 4 / 8) with 128; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
  apply (proj1 (HFSpres o ltac:(change (1024 / 8) with 128; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 4 / 8) with 128; rewrite E529, RF; evalE AG; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob276 Hob277; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* The frame's header words (0x80b14 .. 0x80b1c) and its 104 shadow bytes (0x80b2c .. 0x80cd0), up to the branch
   at 0x80cd4. The shadow region is written, so this run takes the plain engine (no shadow tokens). *)
paj_run_to_shc RUNTOP HS HJ2 0x2c8. { awrFL AG fpos F EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
(* 0x80cd4: the jump to the release of an input of 2 ^ 26 bytes or more is not taken, because
   the caller's input block is shorter than that (ge_base). *)
gh_branch BR HS.
2:{ exfalso. rewrite branch_eq_U in Hc.
    rewrite (gh_U_srl _ _ 26 ltac:(lia)) in Hc.
    rewrite (U_atom _ 11%nat n) in Hc by (first [rewrite (AG 11%nat) by lia; exact E11 | clear - Hn26; lia]).
    rewrite (U_lit _ 0) in Hc by lia.
    rewrite (Z.div_small n (2 ^ 26)) in Hc by (clear - Hn26; lia).
    cbn in Hc. discriminate Hc. }
clear Hc.
(* 0x80d00 (sp1 + 72 := F) and the slot at 0x80d04: the state the next phase starts from. *)
paj_run_to_shc RUNTOP HS HJ2 0x2c8. { awrFL AG fpos F EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msG ?mdG) _ => set (msF := msG) in *; set (mdF := mdG) in * end.
(* ---- the invariant at 0x80d04 ---- *)
gh_region HS 60%nat HR60. gh_region HS 2%nat HR2.
gh_region HS 516%nat HR516. gh_region HS 529%nat HR529.
destruct (al_flag _ _ LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (_ & _ & HFLapp & HFLlt).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (B60 : bv_unsigned (ew Ev 60) = sp1)
    by (rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
  assert (B2 : bv_unsigned (ew Ev 2%nat) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
  assert (B516 : bv_unsigned (ew Ev 516) = F)
    by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia);
  assert (B529 : bv_unsigned (ew Ev 529) = SHADOW_OFF + F / 8)
    by (rewrite E529; apply unsigned_lit_small; change SHADOW_OFF with SB; unfold SB; lia);
  assert (E32f : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32)
end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (EE5 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew Ev nn = getr regs r)
    by (intros nn r Hn; pose proof (bv_unsigned_in_range 5 r) as Hb5;
        change (bv_modulus 5) with 32 in Hb5;
        rewrite (AG nn) by lia; exact (EE nn r Hn))
end.
pose proof HS as HSc.
destruct HSc as (Hfregs & Hpcv & Hsvc & Hresv & Hfcsr & Hrom & Hregsok & Hmemok & Hfactsok).
cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
     PaRun.abs_ss setpc ss_pc ss_resv resv_denot] in Hfregs, Hpcv, Hsvc, Hresv, Hfcsr, Hrom.
(* the registers the next phase reads *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
rewrite (AG 2%nat) in Q8 by lia. rewrite (AG 3%nat) in Q3 by lia. rewrite (AG 4%nat) in Q4 by lia.
rewrite (AG 10%nat) in Q18 by lia. rewrite (AG 11%nat) in Q20 by lia.
rewrite E60 in Q2, Q9. rewrite RF in Q21. rewrite E529 in Q19.
rewrite E10 in Q18. rewrite E11 in Q20.
(* the caller's input block, which this segment does not write *)
assert (GARR : garr8 SEGS (mrestrict (w_H W) (ms_mem msF)) p (map (fun b : byte => bv_unsigned b) pl)).
{ pose proof (map_length (fun b : byte => bv_unsigned b) pl) as Hml.
  destruct Hpn as [[Hn0 Hpe] | [Hnpos Hin]].
  - intros j Hj. exfalso. clear - Hj Hml Hn0. unfold n in Hn0. lia.
  - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    apply (gh_garr_keep (w_H W) mem (ms_mem msF) p _); [|exact HPL].
    intros j Hj.
    apply (F2 p n (Z.of_nat j) Hin ltac:(rewrite Eab; exact Hin));
    [ unfold req_size; destruct (Z.eqb_spec n 0) as [Hzz|Hzz];
      [ clear - Hnpos Hzz; lia | clear - Hj Hml Hnpos; unfold n in *; lia ]
    | intros (r & [] & _) ]. }
apply (HM (mkECX ly S W regs mem md p pl sp1 E0 T) fpos 0 0 ly S2 W msF mdF HB HJ2
  ltac:(rewrite Hfrs2, Hfr0; reflexivity)
  ltac:(cbn [c_S]; rewrite ES2; apply (mo_le_set_fs_r MT MTF); apply (mo_le_refl MT MTL))).
unfold GI_hdr, ge_body, gregs, gsaved, gshadow, gslot, gF, gSH, c_n.
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_sp1 c_E0 c_T].
repeat match goal with |- _ /\ _ => split end.
- unfold GP_hdr. exact Hpcv.
- exact Hresv.
- exact Hsvc.
- exact Hrom.
- exact Hfregs.
- exact Hfcsr.
- rewrite Q2. reflexivity.
- rewrite Q8, (EE 2%nat (2%bv : bv 5) eq_refl). unfold w64, spZ. symmetry. apply Z_to_bv_bv_unsigned.
- rewrite Q9. reflexivity.
- rewrite Q3. apply (EE 3%nat (3%bv : bv 5) eq_refl).
- rewrite Q4. apply (EE 4%nat (4%bv : bv 5) eq_refl).
- exact (proj1 (gh_saved_of _ (w_H W) (ms_mem msF) (spZ regs) regs _ _ _ _ _ HR2 B2 EE5
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity))).
- exact (proj2 (gh_saved_of _ (w_H W) (ms_mem msF) (spZ regs) regs _ _ _ _ _ HR2 B2 EE5
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity))).
- intros i Hi. unfold shadow_of_addr.
  exact (gh_shadow_bytes _ (w_H W) (ms_mem msF) 529%nat (SHADOW_OFF + F / 8) _ _ _ _ _ GSH_entry
    HR529 B529 ltac:(vm_compute; reflexivity) i Hi).
- exact (gh_word_at _ (w_H W) (ms_mem msF) 516%nat F _ _ _ _ _ 1016 (SOff 528%nat 0) FL HR516 B516
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(unfold in_app, kLowShadowBeg, kHighMemBeg in HFLapp; clear - HFLapp HFLlt C1; lia)).
- vm_compute. reflexivity.
- exact GARR.
- lia.
- lia.
- exact Eab.
- clear - Hn26; lia.
- rewrite Q18. reflexivity.
- rewrite Q20. reflexivity.
- rewrite Q19. unfold shadow_of_addr. reflexivity.
- rewrite Q21. reflexivity.
- exact (gh_word_at _ (w_H W) (ms_mem msF) 60%nat sp1 _ _ _ _ _ 72 (SOff 516%nat 0) F HR60 B60
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(clear - HF4096 HFceil C1; lia)).
- exact (gh_word_at _ (w_H W) (ms_mem msF) 60%nat sp1 _ _ _ _ _ 144 (SOff 32%nat 0) SHADOW_OFF HR60 B60
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E32f, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change SHADOW_OFF with SB; unfold SB; lia)).
- exact (gh_word_at _ (w_H W) (ms_mem msF) 60%nat sp1 _ _ _ _ _ 176 (SOff 516%nat 0) F HR60 B60
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(clear - HF4096 HFceil C1; lia)).
Qed.

(* The phase in the chain's shape (image A's GrantEntryChain.v `ph_head`): the jump to the release at 0x80cd4 is
   never taken on this path (n < 2 ^ 26), so the second premise is not used. *)
Theorem ge_head : forall POST,
  ge_from B MT POST (GI_hdr B) -> ge_from B MT POST (GI_leave B MT) -> ge_start B MT POST.
Proof. intros POST HM _. exact (ge_head0 POST HM). Qed.

End c.
End b.
End a.
