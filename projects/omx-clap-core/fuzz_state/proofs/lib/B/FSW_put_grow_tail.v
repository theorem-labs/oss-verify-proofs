(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 260 of its 308 lines of code are new or changed and 2738 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): the SECOND HALF of put's GROW arm (preset_file.c:454-476, A_put 0x8449c),
   the case `failed = 0 /\ cap < len + n + 1`: from the call of the PROGRAM function fuzz_realloc (A_fuzz_realloc
   0x82bc4, ra = 0x84580) to the `ret` 0x84668, concluding lib/B/FSH_Fn_writer.v put_spec's post. The image-B twin of
   lib/A/FSW_put_grow_tail.v, split over files so that its pieces can be proved side by side:
   - THIS FILE: the resume state, the small facts, and the Section data every piece states its lemma over (put_spec's
     data on the grow arm and the first half's hand-over at the call), with the call-site lemmas pgt_E'_reg,
     pgt_E'_x and pgt_call_regs;
   - lib/B/FSW_put_grow_call.v: pgt_callee_pre (fuzz_realloc's fpreU at the call) and pgt_resume (the state after it
     returns to 0x84580);
   - lib/B/FSW_put_grow_granted.v: pgt_granted (a0 <> 0: the new buffer stored, the fast arm's code from 0x845a0);
   - lib/B/FSW_put_grow_refused.v: pgt_refused (a0 = 0: o->failed := 1, the return);
   - lib/B/FSW_put_grow_src.v: pgt_src_after (the source range after fuzz_realloc);
   - lib/B/FSW_put_grow_close.v: pgt_run, the three outcomes of fuzz_realloc_spec composed into put_spec's post.
   Each piece repeats this file's Section header (the same Variables and Hypotheses, in the same order), so its lemma
   is stated over exactly the data pgt_run holds.

   The route, MEASURED with the token engine on B (lane scratch probe, a build machine workspace (internal path),
   2026-10-29T09:2xZ; Bx := FSW_K.fs_Bx, Bspan := FSW_K.fs_Bspan):
   - the call-site state is lib/B/FSW_put_grow.v fsw_pg_ssc (a FETCH stop at 535492 = A_fuzz_realloc, sh_j = 0,
     sh_chk = true, sh_obls = []), with ra = 542080, a0 = buf (atom 33), a1 = s6 = c (atom 36), s0 = o, s1 = n, s2 = s,
     s3 = o >> 3, s4 = o + 24, s11 = the shadow address of o;
   - the resume state pgt_ss1 at 542080 = 0x84580 (run_K 52, sh_static_ok true, regions_wf true; frame [sp - 112, sp)
     with its 14 words, o's 32 bytes at atom 8, the callee-saved shadow addresses of o re-seated over atom 8): the run
     stops at once at `beqz a0`, SR_branch BC_EQ (SOff 10 0) (SLit 0);
     * a0 = 0 (fuzz_realloc refused): the run passes the inline check of o + 24 at 0x8466c / 0x84670 (report site
       0x846b4), stores 1 into o->failed and stops at the ret 542312 = 0x84668, SR_jalr (SOff 37 0), sh_obls = [];
     * a0 <> 0 (granted): the run passes the checks of o at 0x84584 / 0x84588 (site 0x846f4) and of o + 16 at
       0x84590 / 0x84594 (site 0x846fc), stores o->buf = a0 and o->cap = c, reloads frame slot 0 (o + 8) into s6,
       passes 0x845a8 and 0x845b0, and stops at UBSan's pointer-overflow check 542144 = 0x845c0,
       SR_branch BC_LTU (SAlu ALU_ADD (SOff 10 0) (SOff 34 0)) (SOff 10 0), with o's region holding
       [0: SOff 10 0; 8: SOff 34 0; 16: SOff 35 0; 24: 0], sh_obls = [].
   B IS NOT A's CODE: A's granted path calls __asan_memcpy right after the stores; B re-joins the fast arm at 0x845a0
   and so meets UBSan's checks 0x845c0 / 0x845d0 before the copy and 0x84604 / 0x84614 / 0x84618 after it.

   TAKEN FROM: lib/A/FSW_put_grow_tail.v at a working branch 860b2fb1188 (the same blob is on
   a working branch f0e2574c33c): pgt_sh / pgt_regs1 / pgt_cs1 / pgt_o1 / pgt_gf1 / pgt_ss1 / pgt_SH1 /
   pgt_xs with B's registers (s3 / s4 swapped) and B's resume pc, the small facts pgt_aview_nonneg .. pgt_new_once
   unchanged, the Section data unchanged, pgt_E'_reg / pgt_E'_x unchanged, pgt_call_regs with B's ra and s3 / s4.

   RULE-24: proves function put (omx-clap-core/fuzz_state, image B = asan-ubsan, entry 0x8449c; the GROW arm)
   (reuse search: proof-index put_holds / put_close_grow / fsw_pg_loop / pgt_run / fsw_pg_entry_run, index v5
   built 2026-10-29T07:26:27Z, plus a git grep with a passing control (put_failed_run) of 599 cold lib/B trees: no
   lib/B/FSW_put_grow* or FSW_put_holds* anywhere; checker a Theorem Labs lane CONFIRM 09:2xZ). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_put FSW_put_grow FSW_put_grow_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the states ================= *)
(* The call site is lib/B/FSW_put_grow.v fsw_pg_ssc (the loop's exit side run to the FETCH of fuzz_realloc, its frame
   carrying the 14 words the entry path leaves: o + 8 at sp - 112 and the 13 saved registers). *)

(* the resume state at 0x84580: atom 8 = o (s0), 9 = n (s1), 10 = a0 (fuzz_realloc's answer), 18 = s (s2);
   33 / 34 / 35 / 36 = the new buffer, len, c, the end of the new text (the fast arm's resume layout, so that
   FSW_put.fsw_pf_ssr serves after the copy); 37 .. 49 the saved words (fsw_pf_cs); 50 / 51 the OLD buf / cap, which
   o still holds at the resume (the refused path stores only o->failed, so its post reads o's other fields off these
   chunks). The callee-saved registers s3 .. s11 (regs 19 .. 27) are re-seated over atom 8 / atom 32 exactly as the
   call site holds them over atom 10 (B: s3 = o >> 3, s4 = o + 24, s5 = o + 16, s6 = c, s7 = the shadow base, s8 /
   s9 / s10 / s11 = the shadow addresses of o + 8 / o + 24 / o + 16 / o): the post-call code checks o's shadow
   through them. *)
Definition pgt_sh (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 k) (SLit 3)) (SOff 32 0).
Definition pgt_regs1 : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    19%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3))) 20%bv (SOff 8 24)) 21%bv (SOff 8 16)) 22%bv (SOff 35 0))
    23%bv (SOff 32 0)) 24%bv (pgt_sh 8)) 25%bv (pgt_sh 24)) 26%bv (pgt_sh 16)) 27%bv (pgt_sh 0).
(* frame slot 0 holds o + 8 (MEASURED on B: the grow side spills s6 = o + 8 there at 0x84550 and the granted path
   reloads it at 0x8459c) *)
Definition pgt_cs1 : list YP09.chunk := YP09.mkChunk 0 (CVal 8 (SOff 8 8)) :: fsw_pf_cs.
Definition pgt_o1 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 32 0 32
    [YP09.mkChunk 0 (CVal 8 (SOff 50 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 51 0));
     YP09.mkChunk 24 (CVal 4 (SLit 0))].
Definition pgt_gf1 : list (nat * afact) :=
  [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (34%nat, mkAF 0 (2 ^ 27) 0); (35%nat, mkAF 4096 (2 ^ 27) 0);
   (9%nat, mkAF 0 (2 ^ 27) 0)].
Definition pgt_ss1 : sstate :=
  mkSS 542080 pgt_regs1 (fsT_ret_regions 112 pgt_cs1 [pgt_o1]) None
    (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: pgt_gf1) [] []).
Definition pgt_SH1 : list shent := [mkSHE 8 0 32].
(* the resume env's extra atoms after fs_extraT (atom 32): A's fast-arm xs2 layout (lib/A/FSW_put.v:954-956), the saved
   words read off the call-site env E (atoms 1, 8, 9, 18 .. 27 hold the entry registers there) *)
Definition pgt_xs (E : env) (res len c d ob oc : Z) : list word :=
  [Z_to_bv 64 res; Z_to_bv 64 len; Z_to_bv 64 c; Z_to_bv 64 d;
   ew E 1; ew E 8; ew E 9; ew E 18; ew E 19; ew E 20; ew E 21; ew E 22; ew E 23; ew E 24; ew E 25; ew E 26; ew E 27;
   Z_to_bv 64 ob; Z_to_bv 64 oc].

(* the two numbers each run of the resume state needs, checked here (MEASURED on B: the same 52 as A) *)
Example pgt_ss1_K : run_K 0 fs_Bx pgt_SH1 pgt_ss1 = 52%nat.
Proof. vm_compute. reflexivity. Qed.
Example pgt_ss1_wf : regions_wf (fsT_ret_regions 112 pgt_cs1 [pgt_o1]) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================= small facts ================= *)
Lemma pgt_aview_nonneg : forall (H : word -> bool) (m : word -> option byte) a b,
  aview tfibsegs H m a = Some b -> 0 <= b < 256.
Proof.
intros H m a b E. unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) a) as [x|]; [|discriminate].
cbn [option_map] in E. injection E as <-. pose proof (bv_unsigned_in_range 8 x) as R.
change (bv_modulus 8) with 256 in R. lia.
Qed.
Lemma pgt_rdword_nonneg : forall (H : word -> bool) (m : word -> option byte) a v,
  rdword (aview tfibsegs H m) a = Some v -> 0 <= v.
Proof.
intros H m a v E. unfold rdword in E.
destruct (aview tfibsegs H m a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs H m (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs H m (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs H m (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs H m (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs H m (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs H m (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs H m (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
apply pgt_aview_nonneg in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.
Lemma pgt_rdword_some : forall (H : word -> bool) (m : word -> option byte) a,
  (forall k, 0 <= k < 8 -> aview tfibsegs H m (a + k) <> None) ->
  exists v, rdword (aview tfibsegs H m) a = Some v /\ 0 <= v.
Proof.
intros H m a Hk.
assert (Hs : rdword (aview tfibsegs H m) a <> None).
{ unfold rdword.
  destruct (aview tfibsegs H m a) as [b0|] eqn:E0; [|exfalso; apply (Hk 0); [lia | rewrite Z.add_0_r; exact E0]].
  destruct (aview tfibsegs H m (a + 1)) as [b1|] eqn:E1; [|exfalso; exact (Hk 1 ltac:(lia) E1)].
  destruct (aview tfibsegs H m (a + 2)) as [b2|] eqn:E2; [|exfalso; exact (Hk 2 ltac:(lia) E2)].
  destruct (aview tfibsegs H m (a + 3)) as [b3|] eqn:E3; [|exfalso; exact (Hk 3 ltac:(lia) E3)].
  destruct (aview tfibsegs H m (a + 4)) as [b4|] eqn:E4; [|exfalso; exact (Hk 4 ltac:(lia) E4)].
  destruct (aview tfibsegs H m (a + 5)) as [b5|] eqn:E5; [|exfalso; exact (Hk 5 ltac:(lia) E5)].
  destruct (aview tfibsegs H m (a + 6)) as [b6|] eqn:E6; [|exfalso; exact (Hk 6 ltac:(lia) E6)].
  destruct (aview tfibsegs H m (a + 7)) as [b7|] eqn:E7; [|exfalso; exact (Hk 7 ltac:(lia) E7)].
  discriminate. }
destruct (rdword (aview tfibsegs H m) a) as [v|] eqn:Ev; [|contradiction].
exists v. split; [reflexivity | exact (pgt_rdword_nonneg H m a v Ev)].
Qed.
(* template: lib/A/ACem.v:103-117 rdword_of_val_mem (stated there over any segs; re-proved at tfibsegs) *)
Lemma pgt_rdword_of_val_mem : forall (H : word -> bool) (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview tfibsegs H m) a = Some v.
Proof.
intros H m a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview tfibsegs H m (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply YG0s.le_bytes8. exact Hr.
Qed.
Lemma pgt_unpoison_at : forall U (m1 m2 : word -> option byte) w, m1 w = m2 w -> unpoison U m1 w = unpoison U m2 w.
Proof. intros U m1 m2 w E. unfold unpoison. destruct (in_ush U (bv_unsigned w)); [reflexivity | exact E]. Qed.
Lemma pgt_le_byte1 : forall x, 0 <= x < 256 -> le_byte x 1 0 = x.
Proof.
intros x Hx. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
(* two byte lists read at the same address agree where both are defined *)
Lemma pgt_garr8_nth : forall (m : word -> option byte) p (l1 l2 : list Z) (j : nat),
  garr8 tfibsegs m p l1 -> garr8 tfibsegs m p l2 -> (j < length l1)%nat -> (j < length l2)%nat ->
  nth j l1 0 = nth j l2 0.
Proof.
intros m p l1 l2 j H1 H2 Hj1 Hj2.
destruct (H1 j Hj1) as (V1 & R1). destruct (H2 j Hj2) as (V2 & R2).
specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)).
rewrite V1 in V2.
apply (f_equal (fun o0 : option byte => match o0 with Some b => bv_unsigned b | None => 0 end)) in V2.
cbv beta iota in V2. rewrite !Z_to_bv_unsigned in V2. unfold bv_wrap in V2.
rewrite !pgt_le_byte1 in V2 by lia.
change (bv_modulus 8) with 256 in V2. rewrite !Z.mod_small in V2 by lia. lia.
Qed.
(* the k bytes at p, as a list, where all are present *)
Definition pgt_bytes (m : word -> option byte) (p : Z) (k : nat) : list Z :=
  map (fun j => match mbyte tfibsegs m (p + Z.of_nat j) with Some b => bv_unsigned b | None => 0 end) (seq 0 k).
Lemma pgt_bytes_ok : forall (m : word -> option byte) p k,
  (forall j, (j < k)%nat -> mbyte tfibsegs m (p + Z.of_nat j) <> None) ->
  length (pgt_bytes m p k) = k /\ garr8 tfibsegs m p (pgt_bytes m p k).
Proof.
intros m p k Hk. unfold pgt_bytes.
set (F := fun j0 : nat => match mbyte tfibsegs m (p + Z.of_nat j0) with Some b => bv_unsigned b | None => 0 end).
rewrite length_map, length_seq. split; [reflexivity|].
intros j Hj. rewrite length_map, length_seq in Hj.
rewrite (nth_indep (map F (seq 0 k)) 0 (F 0%nat)) by (rewrite length_map, length_seq; exact Hj).
rewrite map_nth, seq_nth by exact Hj. cbn [Nat.add]. unfold F.
destruct (mbyte tfibsegs m (p + Z.of_nat j)) as [b|] eqn:Eb; [|exfalso; exact (Hk j Hj Eb)].
pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
split; [|lia].
intros k0 Hk0. assert (k0 = 0)%nat by lia. subst k0.
replace (p + Z.of_nat j + Z.of_nat 0) with (p + Z.of_nat j) by lia. rewrite Eb. f_equal.
rewrite pgt_le_byte1 by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* fs's alloc.c statics (FS_PSTAT_FP) are image bytes, and none of them is read-only *)
Lemma pgt_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha). apply fsw_pf_in_img. unfold FS_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma pgt_pstat_not_ro : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
assert (HC : forallb (fun r => forallb (fun sg => seg_writable sg || (snd r <=? Z.of_N (seg_base sg))
                                  || (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) tfibsegs
                               && ((snd r <=? FS_RLO) || (FS_RHI <=? fst r))) FS_PSTAT_FP = true)
  by (vm_compute; reflexivity).
intros a Hro (r & Hr & Ha). rewrite forallb_forall in HC. specialize (HC r Hr).
apply andb_prop in HC as [HC1 HC2].
destruct Hro as [(sg & Hsg & Hw & Hin) | Hrl].
- rewrite forallb_forall in HC1. specialize (HC1 sg Hsg). rewrite Hw in HC1. cbn [orb] in HC1.
  apply orb_prop in HC1 as [HC1 | HC1]; apply Z.leb_le in HC1; lia.
- apply orb_prop in HC2 as [HC2 | HC2]; apply Z.leb_le in HC2; lia.
Qed.
(* two blocks of one AR state that start at the same address have the same size *)
Lemma pgt_same_start {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} :
  forall B ly S (W : world tfibsegs) m md p k1 k2,
  AR tfibsegs B ly S W m md -> In (p, k1) (ablocks B ly S) -> In (p, k2) (ablocks B ly S) -> 0 < k1 -> 0 < k2 ->
  k1 = k2.
Proof.
intros B ly S W m md p k1 k2 HAR0 H1 H2 Hk1 Hk2.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (al_blocks _ _ LAWS ly S W m md p k1 HAR0 H1) as (_ & _ & _ & _ & _ & PW & _).
assert (I1 : In (p, req_size k1) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (p, k1)); exact H1).
assert (I2 : In (p, req_size k2) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (p, k2)); exact H2).
pose proof (req_size_pos k1 ltac:(lia)) as (Q1 & _). pose proof (req_size_pos k2 ltac:(lia)) as (Q2 & _).
destruct (Z.eq_dec (req_size k1) (req_size k2)) as [E|E].
- unfold req_size in E. destruct (Z.eqb_spec k1 0), (Z.eqb_spec k2 0); lia.
- destruct (pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros Heq; injection Heq as Heq; exact (E Heq))) as [D|D];
    unfold zdisjoint in D; cbn [fst snd] in D; lia.
Qed.
(* a present byte is visible *)
Lemma pgt_mbyte_present : forall (H : word -> bool) m a, apresent H m a -> mbyte tfibsegs (mrestrict H m) a <> None.
Proof. intros H m a (Hh & b & Hb). unfold mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
(* a nonempty block occurs once in a list of pairwise disjoint block ranges *)
Lemma pgt_new_once : forall (l1 l2 : list (Z * Z)) x, 0 < snd x ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (l1 ++ x :: l2)) -> ~ In x (l1 ++ l2).
Proof.
intros l1 l2 x Hx.
assert (Rx : 0 < req_size (snd x)) by (unfold req_size; destruct (Z.eqb_spec (snd x) 0); lia).
induction l1 as [|y l1 IH]; cbn [app map pairwise]; intros HP Hin.
- destruct HP as (F & _). rewrite Forall_forall in F.
  specialize (F (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) _ x Hin)).
  unfold zdisjoint in F. cbn [fst snd] in F. lia.
- destruct HP as (F & P). destruct Hin as [<- | Hin].
  + rewrite Forall_forall in F.
    assert (Hm : In (fst y, req_size (snd y)) (map (fun b => (fst b, req_size (snd b))) (l1 ++ y :: l2)))
      by (apply (in_map (fun b => (fst b, req_size (snd b)))); apply in_or_app; right; left; reflexivity).
    specialize (F _ Hm). unfold zdisjoint in F. cbn [fst snd] in F. lia.
  + exact (IH P Hin).
Qed.

(* ================= the walk ================= *)
Section pgt. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* S0's shadow-base cells (lib/B/FSH_Base.v FsShadowSyms), the one interceptor contract the granted path calls
   (__asan_memcpy, lib/B/FSH_Rt.v FsRt's fr_memcpy field, as lib/B/FSW_put.v takes it) and the image facts *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis IMG : fs_img_facts tfibsegs B.
(* THE CALLEE: fuzz_realloc's ASan contract, a statement only (lib/B/FSH_Fn_alloc.v, by path from dda8331bd25:
   CTX-free with its `cnt <> fail ->` room guards), discharged at composition. *)
Hypothesis HREALLOC : fuzz_realloc_spec tfibsegs B.

(* ---- put_spec's data, on the grow arm (failed = 0, cap < len + n + 1) ---- *)
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (ot o s n buf cap : Z) (text bs : list Z)
  (live peak cnt fail : Z).
Hypothesis HPRE : fpreU tfibsegs B STK_put ly S U W regs mem md ch.
Hypothesis FH : fs_heads B ly S U.
Hypothesis HHEAD : cap <> 0 -> In (buf - HEAD, HEAD) U.
Hypothesis G10 : getr regs 10 = w64 o.
Hypothesis G11 : getr regs 11 = w64 s.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis HOUT : wout_ok B tfibsegs ly S W mem o buf cap 0 text.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.
Hypothesis Hspo : spZ regs <= o.
Hypothesis Hoot : o + 32 <= ot.
Hypothesis Hot16 : ot mod 16 = 0.
Hypothesis Hottop : ot <= ly_top ly.
Hypothesis HCHN :
  o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
  spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
    rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling).
Hypothesis HPRESENT : forall a, spZ regs <= a < ot -> apresent (w_H W) mem a.
Hypothesis HZS : zbytes_at tfibsegs W mem s bs.
Hypothesis HSK : wsrc_kept B tfibsegs ly S U W mem buf s bs.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis Hbok : WriterSpec.bytes_ok bs.
Hypothesis HSRC : 0 <= s /\ s + n <= alloc_ceiling.
Hypothesis Hsdisj : s + n <= o \/ ot <= s.
Hypothesis HWM : Z.of_nat (length text) + n + 1 <= WMAX.
Hypothesis HCAP : cap <= WMAX.
Hypothesis HCL : cap <= live.
Hypothesis HBUD : wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs).
Hypothesis HGROW : cap < Z.of_nat (length text) + n + 1.

(* ---- the first half's hand-over, at the call of fuzz_realloc (lib/B/FSW_put_grow_run.v fsw_pg_to_call's
   continuation; A's Theorem Labs lane interface) ---- *)
Variables (E' : env) (ms' : machine_state) (mdc : Model) (c : Z).
Hypothesis HS : st_ok tfibsegs E' fsw_pg_ssc (restrict (w_H W) ms').
Hypothesis HJ : ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
  ly S W (unpoison U mem) md [] ly S W (unpoison U (ms_mem ms')) mdc 0.
Hypothesis HARU : ARU tfibsegs B ly S U W (ms_mem ms') mdc.
Hypothesis HMF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
  ms_mem ms' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Hypothesis HPRK : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a.
Hypothesis HEA : YP06.env_agree 36
  (Ereg regs (fs_extraT ++ [Z_to_bv 64 buf; Z_to_bv 64 (Z.of_nat (length text)); Z_to_bv 64 cap])) E'.
Hypothesis HE36 : ew E' 36 = Z_to_bv 64 c.
Hypothesis Hcnew : c = WriterSpec.newcap cap (Z.of_nat (length text) + n + 1).
Hypothesis Hc4096 : 4096 <= c.
Hypothesis HcW : c <= WMAX.
Hypothesis Hcneed : Z.of_nat (length text) + n + 1 <= c.

(* the call-site env's atoms *)
Lemma pgt_E'_reg : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E' j = getr regs r.
Proof.
intros j r Hj Hr. rewrite (proj1 HEA j ltac:(lia)). apply ew_Ereg_nat. exact Hr.
Qed.
Lemma pgt_E'_x : forall (j : nat), (32 <= j < 36)%nat ->
  ew E' j = nth (j - 32) (fs_extraT ++ [Z_to_bv 64 buf; Z_to_bv 64 (Z.of_nat (length text)); Z_to_bv 64 cap])
              (Z_to_bv 64 0).
Proof.
intros j Hj. rewrite (proj1 HEA j ltac:(lia)). replace j with (32 + (j - 32))%nat at 1 by lia.
apply ew_Ereg_extra.
Qed.

(* ---- the call site: the registers fuzz_realloc is entered with ---- *)
Lemma pgt_call_regs :
  ms' = mkst (ms_regs ms') (Z_to_bv 64 A_fuzz_realloc) (ms_mem ms') (seg_rom tfibsegs) /\
  getr (ms_regs ms') 1%bv = Z_to_bv 64 542080 /\ spZ (ms_regs ms') = spZ regs - 112 /\
  getr (ms_regs ms') 3%bv = getr regs 3%bv /\ getr (ms_regs ms') 4%bv = getr regs 4%bv /\
  getr (ms_regs ms') 8%bv = Z_to_bv 64 o /\ getr (ms_regs ms') 9%bv = Z_to_bv 64 n /\
  getr (ms_regs ms') 10%bv = w64 buf /\ getr (ms_regs ms') 11%bv = w64 c /\
  getr (ms_regs ms') 18%bv = Z_to_bv 64 s /\ getr (ms_regs ms') 22%bv = Z_to_bv 64 c /\
  getr (ms_regs ms') 23%bv = Z_to_bv 64 SHADOW_OFF /\
  getr (ms_regs ms') 19%bv = sv_denot E' (SAlu ALU_SRL (SOff 10 0) (SLit 3)) /\
  getr (ms_regs ms') 20%bv = sv_denot E' (SOff 10 24) /\
  getr (ms_regs ms') 21%bv = sv_denot E' (SOff 10 16) /\
  getr (ms_regs ms') 24%bv = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0)) /\
  getr (ms_regs ms') 25%bv = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 32 0)) /\
  getr (ms_regs ms') 26%bv = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 32 0)) /\
  getr (ms_regs ms') 27%bv = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)).
Proof.
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & _).
assert (E10 : ew E' 10 = Z_to_bv 64 o) by (rewrite (pgt_E'_reg 10 10%bv) by (lia || reflexivity); exact G10).
assert (E12 : ew E' 12 = Z_to_bv 64 n) by (rewrite (pgt_E'_reg 12 12%bv) by (lia || reflexivity); exact G12).
assert (E11 : ew E' 11 = Z_to_bv 64 s) by (rewrite (pgt_E'_reg 11 11%bv) by (lia || reflexivity); exact G11).
assert (E33 : ew E' 33 = Z_to_bv 64 buf) by (rewrite (pgt_E'_x 33) by lia; reflexivity).
assert (E32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (pgt_E'_x 32) by lia; reflexivity).
split; [exact (st_ok_restrict_mkst tfibsegs (w_H W) E' _ ms' HS eq_refl)|].
split; [pf_reg HS; reflexivity|].
split.
{ assert (E'2 : bv_unsigned (ew E' 2) = spZ regs)
    by (rewrite (pgt_E'_reg 2 2%bv) by (lia || reflexivity); reflexivity).
  unfold spZ at 1. pf_reg HS. change (bv_unsigned (sv_denot E' (SOff 2 (-112)))) with (YP0e.U E' (SOff 2 (-112))).
  rewrite U_SOff, E'2. apply zcanon_id. unfold M64. lia. }
split; [pf_reg HS; rewrite fsw_SOff0; apply pgt_E'_reg; [lia | reflexivity]|].
split; [pf_reg HS; rewrite fsw_SOff0; apply pgt_E'_reg; [lia | reflexivity]|].
split; [pf_reg HS; rewrite fsw_SOff0; exact E10|].
split; [pf_reg HS; rewrite fsw_SOff0; exact E12|].
split; [pf_reg HS; rewrite fsw_SOff0; exact E33|].
split; [pf_reg HS; rewrite fsw_SOff0; exact HE36|].
split; [pf_reg HS; rewrite fsw_SOff0; exact E11|].
split; [pf_reg HS; rewrite fsw_SOff0; exact HE36|].
split; [pf_reg HS; rewrite fsw_SOff0; exact E32|].
split; [pf_reg HS; reflexivity|].
split; [pf_reg HS; reflexivity|].
split; [pf_reg HS; reflexivity|]. split; [pf_reg HS; reflexivity|]. split; [pf_reg HS; reflexivity|].
split; [pf_reg HS; reflexivity|]. pf_reg HS; reflexivity.
Qed.

End pgt.
