(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 1917 of its 1994 lines of code are new or changed and 2709 lines of the source are left out. *)
(* fs WRITER walk, image A (fs.asan): the SECOND HALF of put's GROW arm (preset_file.c:454-476, A_put 0x8418c), the
   case `failed = 0 /\ cap < len + n + 1`: from the call of the PROGRAM function fuzz_realloc (A_fuzz_realloc
   0x829e8, ra = 0x84268) to the `ret` 0x84314, concluding lib/A/FSH_Fn_writer.v put_spec's post.

   The route, MEASURED with the token engine (VM workspace (internal path) on a build machine, over the pinned
   originals sha256 64b53ff8... fs.asan and 5ac5ce09... fs.asan-ubsan; Bx := FSW_K.fs_Bx, Bspan := FSW_K.fs_Bspan):
   - the call-site state is FSW_put_grow.fsw_pg_ssc (the loop head's BC_GEU side, a FETCH stop at 535016 = A_fuzz_realloc,
     sh_j = 0, sh_chk = true, sh_obls = []), with ra = 541288, a0 = buf (atom 33), a1 = c (atom 36), s0 = o, s1 = n;
   - the resume state pgt_ss1 at 541288 (frame [sp - 112, sp) with its 14 words, o's 32 bytes at atom 8, the
     callee-saved shadow addresses of o re-seated over atom 8): the run stops at once at `beqz a0`
     (SR_branch BC_EQ (SOff 10 0) (SLit 0));
     * a0 = 0 (fuzz_realloc refused): the run stores 1 into o->failed and stops at the ret 541460 = 0x84314
       (SR_jalr (SOff 37 0)), sh_obls = [];
     * a0 <> 0 (granted): the run stores o->cap = c, o->buf = a0, reloads frame slot 0 (o + 8) and stops at the
       FETCH of __asan_memcpy (PC_memcpy 335136) with ra = 541364, a0 = a0 + len, a1 = s, a2 = n, sh_obls = [];
       after the copy the fast arm's resume state FSW_put.fsw_pf_ssr applies with buf := the new buffer and
       cap := c (its run to the ret is the fast arm's run 3).
   Template, cited not copied: lib/A/FSW_put.v put_fast_run (:757-1300, the memcpy call, the resume after it and the
   return), lib/A/FSW_K3.v fsw_after_callFPU_args (:323-427, the resume after a PROGRAM call: here the caller's
   journal has the raised window top ot (FSH_Fn_FORM.md 3a) while put's frame top is sp, so the resume state is
   built with entry_st_ok_full as FSW_K3 does, the journals composed with FSW_K3.fsw_ajournal_sub5); the bespoke
   ASan line a working branch lib/A/Prog/put.v Section Grow :1101-1824 and put_blocks.v :356-538
   were read for the order of the steps only (a different engine: bridging is ruled out, pfb_cut_gap).
   Rule 24: put has released proofs for fs's plain and ubsan builds only, none for ASan (lookup
   (internal path) and r24-0x8418c.txt); fuzz_realloc's ASan contract
   is a statement only (lib/A/FSH_Fn_alloc.v fuzz_realloc_spec), held here as a named Section hypothesis. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_rd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc
FSW_K FSW_K3 FSW_ret FSW_writer_tbl FSW_put FSW_put_grow FSW_put_grow_model FSW_put_close.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the states ================= *)
(* The call site is a Theorem Labs lane's FSW_put_grow.fsw_pg_ssc (the loop's exit side run to the FETCH of fuzz_realloc, its
   frame carrying the 14 words the entry path leaves: o + 8 at sp - 112 and the 13 saved registers). *)

(* the resume state at 0x84268: atom 8 = o (s0), 9 = n (s1), 10 = a0 (fuzz_realloc's answer), 18 = s (s2);
   33 / 34 / 35 / 36 = the new buffer, len, c, the end of the new text (the fast arm's resume layout, so that
   FSW_put.fsw_pf_ssr serves after the copy); 37 .. 49 the saved words (fsw_pf_cs); 50 / 51 the OLD buf / cap, which
   o still holds at the resume (the refused path stores only o->failed, so its post reads o's other fields off these
   chunks). The callee-saved shadow addresses s3 .. s11 (regs 19 .. 27) are re-seated over atom 8 / atom 32 exactly
   as the call site holds them over atom 10: the post-call code checks o's shadow through them (MEASURED:
   SR_load (Some 25 / 27) without them). *)
Definition pgt_sh (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 k) (SLit 3)) (SOff 32 0).
Definition pgt_regs1 : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    19%bv (SOff 8 24)) 20%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3))) 21%bv (SOff 8 16)) 22%bv (SOff 35 0))
    23%bv (SOff 32 0)) 24%bv (pgt_sh 8)) 25%bv (pgt_sh 24)) 26%bv (pgt_sh 16)) 27%bv (pgt_sh 0).
(* frame slot 0 holds o + 8 (MEASURED: the grow side stores it at 0x8423c and the granted path reloads it) *)
Definition pgt_cs1 : list YP09.chunk := YP09.mkChunk 0 (CVal 8 (SOff 8 8)) :: fsw_pf_cs.
Definition pgt_o1 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 32 0 32
    [YP09.mkChunk 0 (CVal 8 (SOff 50 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 51 0));
     YP09.mkChunk 24 (CVal 4 (SLit 0))].
Definition pgt_gf1 : list (nat * afact) :=
  [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (34%nat, mkAF 0 (2 ^ 27) 0); (35%nat, mkAF 4096 (2 ^ 27) 0);
   (9%nat, mkAF 0 (2 ^ 27) 0)].
Definition pgt_ss1 : sstate :=
  mkSS 541288 pgt_regs1 (fsT_ret_regions 112 pgt_cs1 [pgt_o1]) None
    (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: pgt_gf1) [] []).
Definition pgt_SH1 : list shent := [mkSHE 8 0 32].
(* the resume env's extra atoms after fs_extraT (atom 32): the fast arm's xs2 layout (FSW_put.v:954-956), the saved
   words read off the call-site env E (atoms 1, 8, 9, 18 .. 27 hold the entry registers there) *)
Definition pgt_xs (E : env) (res len c d ob oc : Z) : list word :=
  [Z_to_bv 64 res; Z_to_bv 64 len; Z_to_bv 64 c; Z_to_bv 64 d;
   ew E 1; ew E 8; ew E 9; ew E 18; ew E 19; ew E 20; ew E 21; ew E 22; ew E 23; ew E 24; ew E 25; ew E 26; ew E 27;
   Z_to_bv 64 ob; Z_to_bv 64 oc].

(* the two numbers each run of the resume state needs, checked here *)
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
(* S0's shadow-base cells (FSH_Base.v:119), the one interceptor contract the granted path calls (__asan_memcpy,
   FSH_Rt.v FsRt's fr_memcpy field, as a working branch 49c7970f491's put walk takes it) and the image facts *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis IMG : fs_img_facts tfibsegs B.
(* THE CALLEE: fuzz_realloc's ASan contract, a statement only (lib/A/FSH_Fn_alloc.v, CTX-free with its
   `cnt <> fail ->` room guards since a working branch 77f319b4b0e), discharged at composition. *)
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

(* ---- the first half's hand-over, at the call of fuzz_realloc (a Theorem Labs lane's interface) ---- *)
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
  getr (ms_regs ms') 1%bv = Z_to_bv 64 541288 /\ spZ (ms_regs ms') = spZ regs - 112 /\
  getr (ms_regs ms') 3%bv = getr regs 3%bv /\ getr (ms_regs ms') 4%bv = getr regs 4%bv /\
  getr (ms_regs ms') 8%bv = Z_to_bv 64 o /\ getr (ms_regs ms') 9%bv = Z_to_bv 64 n /\
  getr (ms_regs ms') 10%bv = w64 buf /\ getr (ms_regs ms') 11%bv = w64 c /\
  getr (ms_regs ms') 18%bv = Z_to_bv 64 s /\ getr (ms_regs ms') 22%bv = Z_to_bv 64 c /\
  getr (ms_regs ms') 23%bv = Z_to_bv 64 SHADOW_OFF /\
  getr (ms_regs ms') 19%bv = sv_denot E' (SOff 10 24) /\
  getr (ms_regs ms') 20%bv = sv_denot E' (SAlu ALU_SRL (SOff 10 0) (SLit 3)) /\
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

(* ================= piece 1: THE CALLEE'S PRE ================= *)
(* fuzz_realloc's fpreU at the call (FSW_ret.fsw_fpreU_atFP): the callee's sp is sp - 112 inside put's raised window,
   ra = 0x84268, gp / tp kept, and the frame chain from s0 = o built from put_spec's chain clause: o > alloc_ceiling
   (fsw_sp), so a node whose saved next fp is below alloc_ceiling is bad_next and ends the chain. *)
Lemma pgt_callee_pre : exists ch1, fpreU tfibsegs B STK_fuzz_realloc ly S U W (ms_regs ms') (ms_mem ms') mdc ch1.
Proof.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : STK_fuzz_realloc + 112 <= STK_put) by (vm_compute; discriminate).
assert (HSTK0 : 0 <= STK_fuzz_realloc) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & _).
destruct pgt_call_regs as (Ems & R1 & R2 & R3 & R4 & R8 & _).
assert (SB : same_below mem (ms_mem ms') alloc_ceiling) by (intros x Hx; apply HMF; lia).
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms')))
  by exact (arodata_below B W mem (ms_mem ms') SB HRO).
set (rd := aview tfibsegs (w_H W) (unpoison U (ms_mem ms'))).
(* above the frame, the reader at the call is the entry's *)
assert (RDH : forall a, spZ regs <= a < 2 ^ 64 -> rd a = aview tfibsegs (w_H W) (unpoison U mem) a).
{ intros a Ha. unfold rd. apply (aview_at tfibsegs). apply pgt_unpoison_at. apply HMF; lia. }
(* the frame's words at the call, read off the call-site state *)
pose proof (st_ok_mem_ok tfibsegs E' _ _ HS) as (_ & HRS & _).
cbn [ms_mem restrict] in HRS. apply Forall_inv in HRS.
destruct HRS as (_ & _ & _ & HCS). cbn [YP09.r_base YP09.r_chunks base_val] in HCS.
assert (E'2 : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (pgt_E'_reg 2 2%bv) by (lia || reflexivity); reflexivity).
rewrite E'2 in HCS.
rewrite Forall_forall in HCS.
assert (WRA : rdword rd (spZ regs - 8) = Some (raZ regs)).
{ assert (Hc : YP09.chunk_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms')) (spZ regs)
                 (YP09.mkChunk (-8) (CVal 8 (SOff 1 0))))
    by (apply HCS; repeat (first [left; reflexivity | right])).
  pose proof (val_of_chunk_ok tfibsegs E' _ (spZ regs) (-8) 8 (SOff 1 0) (raZ regs) Hc) as Hv.
  assert (Hra64 : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; apply u64_range).
  specialize (Hv ltac:(rewrite fsw_SOff0, (pgt_E'_reg 1 1%bv) by (lia || reflexivity); unfold raZ;
                       symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)).
  replace (spZ regs + -8) with (spZ regs - 8) in Hv by lia.
  rewrite <- (pgt_rdword_of_val_mem (w_H W) (ms_mem ms') (spZ regs - 8) (raZ regs) Hv Hra64).
  apply rdword_ext. intros k Hk. unfold rd.
  apply (fsw_aview_unpoison_high B ly S U W (ms_mem ms') mdc _ HARU). lia. }
pose proof Hstk as (Hsp16 & HSTKa & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Ho16 : o < ly_top ly - 16) by lia.
assert (HCH1 : exists ch1, achain ly rd (spZ (ms_regs ms')) (s0Z (ms_regs ms')) ch1).
{ unfold s0Z. rewrite R8, R2, (wz o) by lia.
  destruct HCHN as [(Ho & Hral) | (Ho & ra & nfp & Hra' & Hnfp & Hor)].
  - (* o right above put's frame: o - 16 is put's own saved ra *)
    destruct (pgt_rdword_some (w_H W) (unpoison U (ms_mem ms')) (o - 8)) as (v & Hv & Hv0).
    { intros k Hk. fold rd. rewrite RDH by lia.
      apply (aview_some_of_apresent tfibsegs). destruct (HPRESENT (o - 8 + k) ltac:(lia)) as (Hh & b & Hb).
      split; [exact Hh|]. unfold unpoison.
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 (o - 8 + k)))); [exists (Z_to_bv 8 0); reflexivity | exists b; exact Hb]. }
    fold rd in Hv.
    destruct (Z_lt_ge_dec v 4096) as [Hv4 | Hv4].
    + exists []. right. split; [lia|]. split; [exact Ho16|]. split; [exact Ho8|]. split; [|constructor].
      cbn [fpchain]. exists v. split; [exact Hv | lia].
    + exists [(o, v, raZ regs)]. right. split; [lia|]. split; [exact Ho16|]. split; [exact Ho8|]. split.
      * cbn [fpchain]. split; [reflexivity|]. split; [exact Ho8|]. split; [exact Hv|].
        split; [replace (o - 16) with (spZ regs - 8) by lia; exact WRA|]. split; [lia|].
        assert (Hb : bad_next o (ly_top ly) (raZ regs) = true)
          by (unfold bad_next; rewrite (proj2 (Z.leb_le (raZ regs) o)) by lia; reflexivity).
        rewrite Hb. exact eq_refl.
      * constructor; [cbn [fst]; lia | constructor].
  - (* the chain from o ends after one node, both words in the caller's frame *)
    assert (Rd8 : rdword rd (o - 8) = Some ra) by (rewrite <- Hra'; apply rdword_ext; intros k Hk; apply RDH; lia).
    assert (Rd16 : rdword rd (o - 16) = Some nfp) by (rewrite <- Hnfp; apply rdword_ext; intros k Hk; apply RDH; lia).
    pose proof (pgt_rdword_nonneg _ _ _ _ Hra') as Hra0.
    destruct (Z_lt_ge_dec ra 4096) as [Hr4 | Hr4].
    + exists []. right. split; [lia|]. split; [exact Ho16|]. split; [exact Ho8|]. split; [|constructor].
      cbn [fpchain]. exists ra. split; [exact Rd8 | lia].
    + destruct Hor as [Hor | Hor]; [lia|].
      exists [(o, ra, nfp)]. right. split; [lia|]. split; [exact Ho16|]. split; [exact Ho8|]. split.
      * cbn [fpchain]. split; [reflexivity|]. split; [exact Ho8|]. split; [exact Rd8|]. split; [exact Rd16|].
        split; [lia|].
        assert (Hb : bad_next o (ly_top ly) nfp = true)
          by (unfold bad_next; rewrite (proj2 (Z.leb_le nfp o)) by lia; reflexivity).
        rewrite Hb. reflexivity.
      * constructor; [cbn [fst]; lia | constructor]. }
destruct HCH1 as (ch1 & HCH1). exists ch1.
apply (fsw_fpreU_atFP B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W (unpoison U mem) md []
  ly S W (ms_mem ms') mdc 0 (ms_regs ms') STK_fuzz_realloc (spZ regs - 112 - ot) ch1 HJ HARU HRO').
- rewrite R2. lia.
- lia.
- lia.
- exact HSTK0.
- lia.
- unfold YK0s.ret_ok. rewrite R1. apply bv_eq. vm_compute. reflexivity.
- unfold raZ. rewrite R1, wz; lia.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- exact HCH1.
Qed.

(* ================= piece 2: THE RESUME ================= *)
(* fuzz_realloc has returned to 0x84268: the caller's journal (window top ot) composed with the callee's
   (FSW_K3.fsw_ajournal_sub5, the callee's FP1 under fsw_fp_sub), ARU at the callee's heads U2, and the resume state
   pgt_ss1 on the memory after the call. FSW_K3.fsw_after_callFPU_args ties the frame top to the journal top sp0;
   put's journal top is ot > sp, so the state is built here with entry_st_ok_full as that lemma builds its own
   (FSW_K3.v:386-427): the frame's 14 words and o's len / failed fields read off the call site and kept by the
   callee journal's frames clause (at or above alloc_ceiling, outside [sp - 112 - STK_fuzz_realloc, sp - 112)), the
   shadow-base cells from AR, then the nine re-seated callee-saved registers (st_ok_set_reg). *)
Lemma pgt_resume : forall FP1 kc ly2 S2 U2 W2 regs2 mem2 md2 res d,
  ajournal tfibsegs B STK_fuzz_realloc (spZ (ms_regs ms')) FP1 ly S W (unpoison U (ms_mem ms')) mdc []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc ->
  fsw_fp_sub B ly S ly S [] (FS_PSTAT_FP ++ wbuf_fp buf cap) FP1 ->
  upoison_ok B ly2 S2 U2 -> upoisoned tfibsegs W2 mem2 U2 ->
  aregs_preserved (ms_regs ms') regs2 ->
  ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc /\
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 /\
  (forall a, spZ regs <= a < 2 ^ 64 ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a) /\
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pgt_xs E' res (Z.of_nat (length text)) c d buf cap)) pgt_ss1
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 541288) mem2 (seg_rom tfibsegs))).
Proof.
intros FP1 kc ly2 S2 U2 W2 regs2 mem2 md2 res d HJc HFP OK2 PO2 HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : STK_fuzz_realloc + 112 <= STK_put) by (vm_compute; discriminate).
assert (HSTK0 : 0 <= STK_fuzz_realloc) by (vm_compute; discriminate).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp16 & HSTKa & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
destruct pgt_call_regs as (Ems & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & R18 & R22 & R23 & R19 & R20 & R21 &
  R24 & R25 & R26 & R27).
assert (E'10 : ew E' 10 = Z_to_bv 64 o) by (rewrite (pgt_E'_reg 10 10%bv) by (lia || reflexivity); exact G10).
assert (E'32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (pgt_E'_x 32) by lia; reflexivity).
assert (E'2 : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (pgt_E'_reg 2 2%bv) by (lia || reflexivity); reflexivity).
(* the composed journal and ARU after the call *)
assert (HJ2 : ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
    (unpoison U mem) md [] ly2 S2 W2 (unpoison U2 mem2) md2 kc).
{ pose proof (fsw_ajournal_sub5 B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
    (unpoison U mem) md [] ly S W (unpoison U (ms_mem ms')) mdc 0 STK_fuzz_realloc (spZ (ms_regs ms')) FP1 []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc HJ HJc ltac:(rewrite R2; lia) ltac:(rewrite R2; lia) HFP) as H.
  rewrite Z.add_0_l in H. exact H. }
assert (HARU2 : ARU tfibsegs B ly2 S2 U2 W2 mem2 md2) by (split; [exact (proj1 HJ2) | split; [exact OK2 | exact PO2]]).
split; [exact HJ2|]. split; [exact HARU2|].
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
(* every byte at or above put's frame is the call's after fuzz_realloc, and at or above sp the entry's *)
assert (KEEPC : forall a, spZ regs - 112 <= a < 2 ^ 64 ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms')) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs).
  rewrite <- (fsw_aview_unpoison_high B ly2 S2 U2 W2 mem2 md2 a HARU2) by lia.
  rewrite <- (fsw_aview_unpoison_high B ly S U W (ms_mem ms') mdc a HARU) by lia.
  apply F1; [lia | rewrite R2; lia]. }
assert (KEEPE : forall a, spZ regs <= a < 2 ^ 64 ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. rewrite (KEEPC a) by lia. unfold mbyte, mrestrict. rewrite (HMF a) by lia. reflexivity. }
split; [exact KEEPE|].
(* the frame words at the call *)
pose proof (st_ok_mem_ok tfibsegs E' _ _ HS) as (_ & HRS & _).
cbn [ms_mem restrict] in HRS. apply Forall_inv in HRS.
destruct HRS as (_ & _ & _ & HCS). cbn [YP09.r_base YP09.r_chunks base_val] in HCS.
rewrite E'2 in HCS. rewrite Forall_forall in HCS.
set (len := Z.of_nat (length text)) in *.
set (Er := Ereg regs2 (fs_extraT ++ pgt_xs E' res len c d buf cap)).
assert (P2 : getr regs2 2%bv = getr (ms_regs ms') 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr (ms_regs ms') 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9%bv = getr (ms_regs ms') 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (F2 : bv_unsigned (ew Er 2) = spZ regs - 112).
{ unfold Er. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2. exact R2. }
assert (F8 : ew Er 8 = Z_to_bv 64 o) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8; exact R8).
assert (F9 : ew Er 9 = Z_to_bv 64 n) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9; exact R9).
assert (F32 : ew Er 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold Er; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F34 : ew Er 34 = Z_to_bv 64 len) by (unfold Er; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F35 : ew Er 35 = Z_to_bv 64 c) by (unfold Er; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F50 : ew Er 50 = Z_to_bv 64 buf)
  by (unfold Er; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F51 : ew Er 51 = Z_to_bv 64 cap)
  by (unfold Er; change 51%nat with (32 + 19)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Hlen0 : 0 <= len) by (unfold len; lia).
assert (Hn0 : 0 <= n) by lia.
assert (F8u : bv_unsigned (ew Er 8) = o) by (rewrite F8; apply wz; lia).
assert (F9u : bv_unsigned (ew Er 9) = n) by (rewrite F9; apply wz; unfold WMAX in *; lia).
assert (F32u : bv_unsigned (ew Er 32) = SHADOW_OFF) by (rewrite F32; apply wz; unfold SHADOW_OFF; lia).
assert (F34u : bv_unsigned (ew Er 34) = len) by (rewrite F34; apply wz; unfold WMAX in *; lia).
assert (F35u : bv_unsigned (ew Er 35) = c) by (rewrite F35; apply wz; unfold WMAX in *; lia).
(* a saved word of the call's frame is the resume frame's chunk *)
assert (CM : forall o0 (k j : nat), ew Er j = ew E' k ->
  YP09.chunk_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms')) (spZ regs) (YP09.mkChunk o0 (CVal 8 (SOff k 0))) ->
  -112 <= o0 -> o0 + 8 <= 0 ->
  YP09.chunk_ok tfibsegs Er (mrestrict (w_H W2) mem2) (spZ regs - 112) (YP09.mkChunk (o0 + 112) (CVal 8 (SOff j 0)))).
{ intros o0 k j Hjk Hck Ho1 Ho2.
  apply (fsw_pf_chunk_move E' Er _ _ (spZ regs) (spZ regs - 112) o0 (o0 + 112) 8 (SOff k 0) (SOff j 0) Hck).
  - rewrite !fsw_SOff0. exact Hjk.
  - lia.
  - intros i Hi. cbn [Z.of_N] in Hi. apply KEEPC. lia. }
assert (C0 : YP09.chunk_ok tfibsegs Er (mrestrict (w_H W2) mem2) (spZ regs - 112) (YP09.mkChunk 0 (CVal 8 (SOff 8 8)))).
{ apply (fsw_pf_chunk_move E' Er _ _ (spZ regs) (spZ regs - 112) (-112) 0 8 (SOff 10 8) (SOff 8 8)
    (HCS (YP09.mkChunk (-112) (CVal 8 (SOff 10 8))) ltac:(repeat (first [left; reflexivity | right])))).
  - cbn [sv_denot]. rewrite F8, E'10. reflexivity.
  - lia.
  - intros i Hi. cbn [Z.of_N] in Hi. apply KEEPC. lia. }
(* the shadow-base cells on the memory after the call (as FSW_put.v:985-1003) *)
destruct (fsw_got_shadow B ly2 S2 W2 (unpoison U2 mem2) md2 (proj1 HSS) (proj2 HSS) (proj1 HARU2)) as [Kgot Kcell].
assert (MBL : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) x = mbyte tfibsegs (mrestrict (w_H W2) (unpoison U2 mem2)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly2 S2 U2 W2 mem2 md2 (Z_to_bv 64 x) HARU2
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W2) (unpoison U2 mem2)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. rewrite (MBL (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W2) mem2) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W2) (unpoison U2 mem2) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W2) mem2) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W2) (unpoison U2 mem2) _ _ Kcell)]. }
(* the resume state with every register its own atom *)
assert (HSR0 : st_ok tfibsegs Er
    (mkSS 541288 sr_atoms (fsT_ret_regions 112 pgt_cs1 [pgt_o1]) None
      (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: pgt_gf1) [] []))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 541288) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); fold Er.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold fsT_ret_regions. cbn [app].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + (* the frame, its 14 words *)
      unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite F2. split; [lia|]. split; [lia|]. split.
      * intros q Hq. apply (apresent_writable tfibsegs).
        apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem2 md2 _ HARU2); [lia|]. apply Hpres2. lia.
      * unfold pgt_cs1, fsw_pf_cs. constructor; [exact C0|].
        repeat constructor.
        all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o2 (CVal 8 (SOff ?j 0))) =>
          let o0 := eval vm_compute in (o2 - 112) in
          let k := eval vm_compute in (if Nat.eqb j 37 then 1%nat else if Nat.eqb j 38 then 8%nat
                                       else if Nat.eqb j 39 then 9%nat else (j - 22)%nat) in
          exact (CM o0 k j eq_refl (HCS (YP09.mkChunk o0 (CVal 8 (SOff k 0)))
                   ltac:(repeat (first [left; reflexivity | right]))) ltac:(lia) ltac:(lia))
        end.
    + (* the GOT word of the shadow base *)
      unfold fs_got_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
      split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
        (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
        [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
    + (* the shadow-base cell *)
      unfold fs_bcell_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
      split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
        [rewrite fsw_SOff0, F32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
    + (* o: its len and failed fields, all 32 bytes writable *)
      unfold pgt_o1, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite F8u. split; [lia|]. split; [lia|]. split.
      { intros q Hq. apply (apresent_writable tfibsegs).
        apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem2 md2 _ HARU2); [lia|]. apply Hpres2. lia. }
      assert (VH2 : forall a k v, spZ regs <= a -> a + Z.of_nat k <= 2 ^ 64 ->
        val_mem tfibsegs (mrestrict (w_H W) mem) a k v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a k v)
        by (intros a k v Ha Hk Hv i Hi; rewrite (KEEPE (a + Z.of_nat i)) by lia; exact (Hv i Hi)).
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val tfibsegs Er _ o 0 8 (SOff 50 0) buf);
          [rewrite fsw_SOff0; exact F50 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | rewrite Z.add_0_r; exact (VH2 o 8%nat buf ltac:(lia) ltac:(lia) Vbuf)].
      * apply (chunk_ok_val tfibsegs Er _ o 8 8 (SOff 34 0) len);
          [rewrite fsw_SOff0; exact F34 | cbn [Z.of_N]; unfold WMAX in *; lia | cbn [Z.of_N]; lia
          | exact (VH2 (o + 8) 8%nat len ltac:(lia) ltac:(lia) Vlen)].
      * apply (chunk_ok_val tfibsegs Er _ o 16 8 (SOff 51 0) cap);
          [rewrite fsw_SOff0; exact F51 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | exact (VH2 (o + 16) 8%nat cap ltac:(lia) ltac:(lia) Vcap)].
      * apply (chunk_ok_val tfibsegs Er _ o 24 4 (SLit 0) 0);
          [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact (VH2 (o + 24) 4%nat 0 ltac:(lia) ltac:(lia) Vfail)].
  - apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pgt_o1, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite F2, F8u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok pgt_gf1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite F2, F32u, F8u, F34u, F35u, F9u.
    change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold WMAX in *. repeat split; lia. }
(* the nine callee-saved registers the post-call code reads, re-seated over atoms 8 / 32 / 35 *)
assert (P19 : getr regs2 19%bv = getr (ms_regs ms') 19%bv) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20%bv = getr (ms_regs ms') 20%bv) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21%bv = getr (ms_regs ms') 21%bv) by exact (HP 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22%bv = getr (ms_regs ms') 22%bv) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23%bv = getr (ms_regs ms') 23%bv) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24%bv = getr (ms_regs ms') 24%bv) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25%bv = getr (ms_regs ms') 25%bv) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26%bv = getr (ms_regs ms') 26%bv) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27%bv = getr (ms_regs ms') 27%bv) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
assert (NZ : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv)
  by (intros r Hr Hz; apply Hr; rewrite Hz; reflexivity).
assert (Q19 : getr regs2 19%bv = sv_denot Er (SOff 8 24)).
{ rewrite P19, R19. cbn [sv_denot]. rewrite E'10, F8. reflexivity. }
assert (Q20 : getr regs2 20%bv = sv_denot Er (SAlu ALU_SRL (SOff 8 0) (SLit 3))).
{ rewrite P20, R20. cbn [sv_denot]. rewrite E'10, F8. reflexivity. }
assert (Q21 : getr regs2 21%bv = sv_denot Er (SOff 8 16)).
{ rewrite P21, R21. cbn [sv_denot]. rewrite E'10, F8. reflexivity. }
assert (Q22 : getr regs2 22%bv = sv_denot Er (SOff 35 0)) by (rewrite P22, R22, fsw_SOff0, F35; reflexivity).
assert (Q23 : getr regs2 23%bv = sv_denot Er (SOff 32 0)) by (rewrite P23, R23, fsw_SOff0, F32; reflexivity).
assert (Q24 : getr regs2 24%bv = sv_denot Er (pgt_sh 8)).
{ rewrite P24, R24. unfold pgt_sh. cbn [sv_denot]. rewrite E'10, E'32, F8, F32. reflexivity. }
assert (Q25 : getr regs2 25%bv = sv_denot Er (pgt_sh 24)).
{ rewrite P25, R25. unfold pgt_sh. cbn [sv_denot]. rewrite E'10, E'32, F8, F32. reflexivity. }
assert (Q26 : getr regs2 26%bv = sv_denot Er (pgt_sh 16)).
{ rewrite P26, R26. unfold pgt_sh. cbn [sv_denot]. rewrite E'10, E'32, F8, F32. reflexivity. }
assert (Q27 : getr regs2 27%bv = sv_denot Er (pgt_sh 0)).
{ rewrite P27, R27. unfold pgt_sh. cbn [sv_denot]. rewrite E'10, E'32, F8, F32. reflexivity. }
assert (N19 : 19%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N20 : 20%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N21 : 21%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N22 : 22%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N23 : 23%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N24 : 24%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N25 : 25%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N26 : 26%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N27 : 27%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
(* one register at a time, the state's projections reduced after each step: st_ok_set_reg's conclusion repeats the
   state five times (ss_pc / ss_regs / ss_mem / ss_resv / ss_facts), so nine unreduced steps grow it as 5 ^ 9 *)
pose proof (st_ok_set_reg tfibsegs Er _ _ 19%bv (SOff 8 24) HSR0 N19 Q19) as H19.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H19. clear HSR0.
pose proof (st_ok_set_reg tfibsegs Er _ _ 20%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3)) H19 N20 Q20) as H20.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H20. clear H19.
pose proof (st_ok_set_reg tfibsegs Er _ _ 21%bv (SOff 8 16) H20 N21 Q21) as H21.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H21. clear H20.
pose proof (st_ok_set_reg tfibsegs Er _ _ 22%bv (SOff 35 0) H21 N22 Q22) as H22.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H22. clear H21.
pose proof (st_ok_set_reg tfibsegs Er _ _ 23%bv (SOff 32 0) H22 N23 Q23) as H23.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H23. clear H22.
pose proof (st_ok_set_reg tfibsegs Er _ _ 24%bv (pgt_sh 8) H23 N24 Q24) as H24.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H24. clear H23.
pose proof (st_ok_set_reg tfibsegs Er _ _ 25%bv (pgt_sh 24) H24 N25 Q25) as H25.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H25. clear H24.
pose proof (st_ok_set_reg tfibsegs Er _ _ 26%bv (pgt_sh 16) H25 N26 Q26) as H26.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H26. clear H25.
pose proof (st_ok_set_reg tfibsegs Er _ _ 27%bv (pgt_sh 0) H26 N27 Q27) as H27.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H27. clear H26.
exact H27.
Qed.

(* ================= piece 3: THE GRANTED TAIL ================= *)
(* fuzz_realloc granted the new buffer res (its p = 0 or p <> 0 arm). From the resume state `beqz a0` falls through,
   put stores o->cap = c and o->buf = res, reloads o + 8 from frame slot 0 and calls __asan_memcpy (res + len, s, n);
   after the copy the fast arm's resume state FSW_put.fsw_pf_ssr applies with buf := res, cap := c, and its run stores
   len + n at o + 8 and the 0 at res + len + n and returns. Template: FSW_put.v put_fast_run :818-1292 (the memcpy
   call, the resume after it, the run to the ret, the post); the buffer is here the NEW block, a temporary block of the
   journal (in the blocks after the call, not in the entry's: awr_byte's in_tmp_block arm), where the fast arm's was
   the old one under wbuf_fp. Everything about the memory after the call is a premise (the composition reads it off
   fuzz_realloc's post and the callee journal); the journal count k is any K at or above the callee's kc. *)
Lemma pgt_granted : forall kc ly2 S2 U2 W2 regs2 mem2 md2 res K,
  ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pgt_xs E' res (Z.of_nat (length text)) c (res + Z.of_nat (length text) + n)
    buf cap))
    pgt_ss1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 541288) mem2 (seg_rom tfibsegs))) ->
  aregs_preserved (ms_regs ms') regs2 ->
  getr regs2 10%bv = w64 res -> 4096 + HEAD <= res ->
  fs_rblock tfibsegs B ly2 S2 W2 mem2 res c -> ~ In (res - HEAD, c + HEAD) (ablocks B ly S) -> fs_heads B ly2 S2 U2 ->
  zbytes_at tfibsegs W2 mem2 res text ->
  (forall a, spZ regs <= a < 2 ^ 64 ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a) ->
  zbytes_at tfibsegs W2 mem2 s bs ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF s n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) mem2) s n) -> amem_range s n ->
  (forall x, s <= x < s + n -> ~ (res - HEAD <= x < res + c)) ->
  (forall i, 0 <= i < n ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)) ->
  fs_glob tfibsegs W2 mem2 (live - cap + c) (Z.max peak (live - cap + c)) (cnt + 1) fail ->
  (exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> kc <= K ->
  SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 541288) mem2 (seg_rom tfibsegs)) md2)
    (fpostU tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md K U2
      (fun ly' S' W' regs' mem' md' =>
         ly' = ly2 /\ S' = S2 /\
         wout_ok B tfibsegs ly' S' W' mem' o res c 0 (text ++ bs) /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
         fs_glob tfibsegs W' mem' (live - cap + c) (Z.max peak (live - cap + c)) (cnt + 1) fail /\
         (forall i, 0 <= i < n ->
            mbyte tfibsegs (mrestrict (w_H W') mem') (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)))).
Proof.
intros kc ly2 S2 U2 W2 regs2 mem2 md2 res K HJ2 HARU2 HS1 HP R10 Hres HRB HNEW FH2 HTXT KEEPE HZS2 SRA2 SHULL2 SAMR
  SDISJ SKEEP HGLOB2 Hcj HKK.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTKa & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HARU2 as HARU2m.
pose proof HSRC as (Hs0 & Hsn).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
destruct pgt_call_regs as (Ems & R1 & R2 & R3 & R4 & R8 & R9 & R10c & R11 & R18 & R22 & R23 & R19 & R20 & R21 &
  R24 & R25 & R26 & R27).
pose proof HRB as (Hin & Hb16 & Hc0 & Vhead).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U2 mem2) md2 (res - HEAD) (c + HEAD) (proj1 HARU2) Hin)
  as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & HbM).
assert (RQB : req_size (c + HEAD) = c + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (c + 16) 0); lia).
rewrite RQB in Hbceil, Hbapp. unfold in_app, kLowShadowBeg, ASAN_CEIL, HEAD in Hbapp. unfold HEAD in Hbceil, Hb4096.
set (len := Z.of_nat (length text)) in *.
assert (Hlen0 : 0 <= len) by (unfold len; lia).
assert (Hn0 : 0 <= n) by lia.
unfold WMAX in HWM, HCAP, HcW.
assert (Ho47 : o + 32 <= 2 ^ 47) by lia.
assert (Hoc : alloc_ceiling + STK_put <= o) by lia.
(* the new buffer's bytes are no image byte *)
assert (BNI : forall t, res <= t < res + c -> ~ in_img tfibsegs t).
{ intros t Ht. apply (blk_img tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 (res - HEAD) (c + HEAD) t (proj1 HARU2) Hin).
  rewrite RQB. unfold HEAD. lia. }
set (d := res + len) in *.
set (Er := Ereg regs2 (fs_extraT ++ pgt_xs E' res len c (d + n) buf cap)) in *.
(* the resume env's atoms *)
assert (P2 : getr regs2 2%bv = getr (ms_regs ms') 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr (ms_regs ms') 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr (ms_regs ms') 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr (ms_regs ms') 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9%bv = getr (ms_regs ms') 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18%bv = getr (ms_regs ms') 18%bv) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
assert (F2 : bv_unsigned (ew Er 2) = spZ regs - 112)
  by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; exact R2).
assert (F3 : ew Er 3 = getr regs 3%bv) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl), P3; exact R3).
assert (F4 : ew Er 4 = getr regs 4%bv) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl), P4; exact R4).
assert (F8 : ew Er 8 = Z_to_bv 64 o) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8; exact R8).
assert (F9 : ew Er 9 = Z_to_bv 64 n) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9; exact R9).
assert (F10 : ew Er 10 = Z_to_bv 64 res) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact R10).
assert (F18 : ew Er 18 = Z_to_bv 64 s) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), P18; exact R18).
assert (F32 : ew Er 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold Er; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F34 : ew Er 34 = Z_to_bv 64 len) by (unfold Er; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F8u : bv_unsigned (ew Er 8) = o) by (rewrite F8; apply wz; lia).
(* o's 32 bytes are addressable on any memory where AR holds over U2: the stack's shadow is 0 (as FSW_put.v:734-747) *)
assert (HLO2 : layout_ok ly2) by exact (am_layout _ _ _ _ (proj1 (proj1 HARU2))).
pose proof (lo_top ly2 HLO2) as LTOP.
assert (Hlo8 : ly_stk_lo ly2 mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & L5 & _). unfold page_aligned in L5.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L5]]. }
assert (Hhi8 : ly_stk_hi ly2 mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & _ & L6 & _). unfold page_aligned in L6.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L6]]. }
assert (RAO : forall (m : word -> option byte) md', ARU tfibsegs B ly2 S2 U2 W2 m md' ->
  range_addressable (aview tfibsegs (w_H W2) m) SHADOW_OFF o 32).
{ intros m md' HARm.
  assert (HZS0 : zero_shadow (aview tfibsegs (w_H W2) (unpoison U2 m)) SHADOW_OFF
                  (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2)).
  { exact (al_zshadow _ _ LAWS ly2 S2 W2 (unpoison U2 m) md'
             (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2) (proj1 HARm) (or_introl eq_refl)). }
  apply (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly2 S2 U2 W2 m md' (w_H W2) o 32 HARm ltac:(lia) ltac:(lia))).
  eapply range_addressable_sub;
    [ apply (zero_shadow_range (aview tfibsegs (w_H W2) (unpoison U2 m)) SHADOW_OFF
               (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2) Hlo8
               ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS0)
    | lia | lia]. }
assert (SHOK1 : sh_ok tfibsegs fs_Bx pgt_SH1 Er (mrestrict (w_H W2) mem2)).
{ unfold pgt_SH1. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W2) mem2 Er fs_Bx 8%nat o 32 o 0 32 (RAO mem2 md2 HARU2)).
  - unfold fs_Bx. apply (U_atom Er 32 SHADOW_OFF F32). unfold SHADOW_OFF; lia.
  - apply (U_atom Er 8 o F8). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. lia. }
(* `beqz a0`: a0 = res <> 0 *)
srr_branch_tok fsw_wr_tbl_ok HS1 SHOK1 fs_Bspan.
{ exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom Er 10 res F10) in Hc by lia.
  assert (U0 : YP0e.U Er (SLit 0) = 0) by reflexivity. rewrite U0 in Hc. apply Z.eqb_eq in Hc. lia. }
(* run 1: the two stores into o, the reload of o + 8, to the call of __asan_memcpy (PC_memcpy, ra = 0x84274) *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS1 HJ2 HARU2 SHOK1 fs_Bspan.
- lazymatch goal with |- context C [ss_mem ?ssx] =>
    let rs' := eval vm_compute in (ss_mem ssx) in
    let g := context C [rs'] in change g end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
    [reflexivity | rewrite F2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
    [reflexivity | rewrite F8u; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil.
- (* the run wrote only put's frame and o *)
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
    ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { intros a Ha H1 H2. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
    vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?F2, ?F8u in Hr; lia. }
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a)
    by (intros a H0 H1 H2; unfold mbyte, mrestrict; rewrite (M1 a H0 H1 H2); reflexivity).
  pose proof (fun a => apresent_grows _ _ _ a HG) as PR1.
  clear HF HFr HG.
  (* ---- the call of __asan_memcpy: its registers ---- *)
  assert (Ems0 : ms = mkst (ms_regs ms) (Z_to_bv 64 PC_memcpy) (ms_mem ms) (seg_rom tfibsegs))
    by exact (st_ok_restrict_mkst tfibsegs (w_H W2) Er _ ms HS1 eq_refl).
  assert (RT1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 541364) by (pf_reg HS1; reflexivity).
  assert (RT2 : spZ (ms_regs ms) = spZ regs - 112) by (unfold spZ at 1; pf_reg HS1; rewrite fsw_SOff0; exact F2).
  assert (RT3 : getr (ms_regs ms) 3%bv = getr regs 3%bv) by (pf_reg HS1; rewrite fsw_SOff0; exact F3).
  assert (RT4 : getr (ms_regs ms) 4%bv = getr regs 4%bv) by (pf_reg HS1; rewrite fsw_SOff0; exact F4).
  assert (RT8 : getr (ms_regs ms) 8%bv = Z_to_bv 64 o) by (pf_reg HS1; rewrite fsw_SOff0; exact F8).
  assert (RT9 : getr (ms_regs ms) 9%bv = Z_to_bv 64 n) by (pf_reg HS1; rewrite fsw_SOff0; exact F9).
  assert (RT10 : getr (ms_regs ms) 10%bv = w64 d).
  { pf_reg HS1. rewrite denot_lit_U. unfold w64. f_equal.
    rewrite U_SAlu, (U_atom Er 10 res F10), (U_atom Er 34 len F34) by lia. cbn [zalu_raw].
    apply zcanon_id. unfold M64, d. lia. }
  assert (RT11 : getr (ms_regs ms) 11%bv = w64 s) by (pf_reg HS1; rewrite fsw_SOff0; exact F18).
  assert (RT12 : getr (ms_regs ms) 12%bv = w64 n) by (pf_reg HS1; rewrite fsw_SOff0; exact F9).
  assert (RT23 : getr (ms_regs ms) 23%bv = Z_to_bv 64 SHADOW_OFF) by (pf_reg HS1; rewrite fsw_SOff0; exact F32).
  (* the frame's words and o's fields at the call, read off the state *)
  pose proof (st_ok_mem_ok tfibsegs Er _ _ HS1) as (_ & HRS1 & _).
  cbn [ms_mem restrict ss_mem] in HRS1.
  pose proof (Forall_inv HRS1) as RF1.
  apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv in HRS1. rename HRS1 into RO1.
  destruct RF1 as (_ & _ & _ & HCF). cbn [YP09.r_base YP09.r_chunks base_val] in HCF.
  rewrite F2 in HCF. rewrite Forall_forall in HCF.
  destruct RO1 as (_ & _ & _ & HCO1). cbn [YP09.r_base YP09.r_chunks base_val] in HCO1.
  rewrite F8u in HCO1. rewrite Forall_forall in HCO1.
  (* the call's premises *)
  assert (LOWT : forall t, 0 <= t < alloc_ceiling -> ms_mem ms (Z_to_bv 64 t) = mem2 (Z_to_bv 64 t))
    by (intros t Ht; apply M1; lia).
  assert (AVT : forall t, 0 <= t < alloc_ceiling ->
    aview tfibsegs (w_H W2) (ms_mem ms) t = aview tfibsegs (w_H W2) mem2 t)
    by (intros t Ht; apply (aview_at tfibsegs); exact (LOWT t Ht)).
  lazymatch type of HARU2 with ARU _ _ _ _ _ _ _ ?mdT =>
    assert (HPREc : ecall_preU tfibsegs B ly2 S2 U2 W2 (ms_regs ms) (ms_mem ms) mdT) end.
  { eapply (fsw_ecall_preU_at B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) (spZ regs - 112 - ot) HJ2 HARU2).
    - rewrite RT2. lia.
    - lia.
    - lia.
    - unfold ESTACK. lia.
    - unfold YK0s.ret_ok. rewrite RT1. apply bv_eq. vm_compute. reflexivity.
    - rewrite RT3. exact Hgp.
    - rewrite RT4. exact Htp. }
  assert (HDEST : dest_ok tfibsegs B ly2 S2 W2 (ms_regs ms) (ms_mem ms) d n).
  { intros a Ha.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U2 (ms_mem ms)) _ (res - HEAD) (c + HEAD) (proj1 HARU2) Hin)
      as (_ & _ & _ & _ & Hbp & _).
    destruct (Hbp a ltac:(rewrite RQB; unfold HEAD, d in *; lia)) as (Hpa & Hno).
    split; [|split; [exact Hno | rewrite RT2; unfold ESTACK, d in *; lia]].
    apply (apresent_writable tfibsegs). destruct Hpa as (Hh & b & Hb). split; [exact Hh|]. exists b.
    rewrite <- (fsw_pf_unp B ly2 S2 U2 W2 (ms_mem ms) _ a HARU2);
      [exact Hb | unfold d in *; lia | unfold d, SHADOW_OFF in *; lia]. }
  assert (HAMRd : amem_range d n) by (unfold amem_range, d in *; lia).
  assert (HRAd : range_addressable (aview tfibsegs (w_H W2) (ms_mem ms)) SHADOW_OFF d n).
  { apply (fsw_pf_ra_raw (w_H W2) U2 (ms_mem ms) d n); [unfold d in *; lia | unfold d in *; lia | |].
    - intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU2))); [unfold d in *; lia|].
      exact (fsw_pf_heads_out B ly2 S2 U2 W2 (unpoison U2 (ms_mem ms)) _ res c x (proj1 HARU2) FH2 Hin Hc0
               ltac:(unfold d in *; lia)).
    - apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 (ms_mem ms)) _ (res - HEAD) (c + HEAD)
        d n (proj1 HARU2) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
  assert (HHULLd : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) (ms_mem ms)) d n).
  { intros Hn1. apply (fsw_pf_hull_raw W2 U2 (ms_mem ms) d n (proj2 (proj2 HARU2)));
      [unfold d in *; lia | unfold d in *; lia |].
    apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 (ms_mem ms)) _ (res - HEAD) (c + HEAD) d n
      (proj1 HARU2) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
  assert (HCPY : 0 <= s /\ s + n <= 2 ^ 63 /\ src_ok tfibsegs W2 (ms_regs ms) (ms_mem ms) s n /\
    (d + n <= s \/ s + n <= d) /\ amem_range s n /\
    range_addressable (aview tfibsegs (w_H W2) (ms_mem ms)) SHADOW_OFF s n /\
    (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) (ms_mem ms)) s n)).
  { split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [|rewrite RT2; unfold ESTACK; lia].
      rewrite AVT by lia. unfold zbytes_at in HZS2.
      destruct (HZS2 (Z.to_nat (a - s)) ltac:(lia)) as (Hv & _). specialize (Hv 0%nat ltac:(lia)).
      replace (s + Z.of_nat (Z.to_nat (a - s)) + Z.of_nat 0) with a in Hv by lia.
      unfold aview. rewrite Hv. discriminate. }
    split.
    { destruct (Z_le_gt_dec (d + n) s); [left; lia|]. destruct (Z_le_gt_dec (s + n) d); [right; lia|].
      exfalso. apply (SDISJ (Z.max s d)); unfold d, HEAD in *; lia. }
    split; [exact SAMR|]. split.
    { eapply range_addressable_agree; [|exact SRA2]. intros x Hx. apply AVT. unfold shadow_of_addr, SHADOW_OFF. lia. }
    intros Hn1 t Ht. rewrite AVT; [exact (SHULL2 Hn1 t Ht)|]. unfold shadow_addr, SHADOW_OFF in Ht. lia. }
  (* the call: __asan_memcpy (d, s, n) by its contract, the journal put back on the memory after it; the copy's
     window is a byte of the NEW block, a temporary block of the journal (in_tmp_block) *)
  rewrite Ems0.
  eapply SRr_bind.
  { apply (fsw_intrin_atU B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
      ly2 S2 U2 W2 (ms_mem ms) _ kc U2
      (fun a => d <= a < d + n \/ spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms)) (w64 (raZ (ms_regs ms))) _
      (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
         (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) mem' (d + i) = aview tfibsegs (w_H W2) (ms_mem ms) (s + i)) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms)) ->
            aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) (ms_mem ms) a) /\
         (forall a, apresent (w_H W2) (ms_mem ms) a -> apresent (w_H W2) mem' a)) HJ2).
    - eapply SRr_mono.
      { exact (RT_memcpy ly2 S2 U2 W2 (ms_regs ms) (ms_mem ms) _ d s n HPREc RT10 RT11 RT12
          ltac:(unfold d in *; lia) ltac:(unfold d in *; lia) ltac:(unfold d in *; lia) HDEST HAMRd HRAd HHULLd HCPY). }
      cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsame & H10 & Hcp & Hfr & Hpr).
      split; [reflexivity|]. exists regs', mem', md'.
      split; [reflexivity|]. split; [exact HARU'|]. split; [exact Hsame|].
      split.
      { intros a Ha HnW.
        destruct (in_ush U2 (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
        - apply (aview_unpoison_in tfibsegs). exact EU.
        - rewrite !(aview_unpoison_out tfibsegs) by exact EU.
          apply Hfr; [exact Ha | intros Hx; apply HnW; left; exact Hx | intros Hx; apply HnW; right; exact Hx]. }
      split.
      { intros a (Hh & b & Hb). split; [exact Hh|].
        destruct (in_ush U2 (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
        - exists (Z_to_bv 8 0). apply unpoison_in. exact EU.
        - rewrite (unpoison_out U2 mem' (Z_to_bv 64 a) EU).
          rewrite (unpoison_out U2 (ms_mem ms) (Z_to_bv 64 a) EU) in Hb.
          destruct (Hpr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
      split; [exact HP'|]. split; [exact Hcp|]. split; [exact Hfr | exact Hpr].
    - intros a [Ha | Ha].
      + left. right. right. left. exists (res - HEAD), (c + HEAD). split; [exact Hin|]. split; [exact HNEW|].
        rewrite RQB. unfold d, HEAD in *. lia.
      + left. left. rewrite RT2 in Ha. unfold ESTACK in Ha. lia. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HARU3 & HP3 & HCP & HFR & HPR).
  (* ---- the resume at 0x84274: FSW_put.fsw_pf_ssr with buf := res, cap := c ---- *)
  assert (ERA : w64 (raZ (ms_regs ms)) = Z_to_bv 64 541364) by (unfold w64, raZ; rewrite RT1, wz; [reflexivity | lia]).
  rewrite ERA.
  assert (S2' : getr regs3 2%bv = getr (ms_regs ms) 2%bv) by exact (HP3 2 ltac:(unfold acallee_saved; lia)).
  assert (S3' : getr regs3 3%bv = getr (ms_regs ms) 3%bv) by exact (HP3 3 ltac:(unfold acallee_saved; lia)).
  assert (S4' : getr regs3 4%bv = getr (ms_regs ms) 4%bv) by exact (HP3 4 ltac:(unfold acallee_saved; lia)).
  assert (S8' : getr regs3 8%bv = getr (ms_regs ms) 8%bv) by exact (HP3 8 ltac:(unfold acallee_saved; lia)).
  assert (S9' : getr regs3 9%bv = getr (ms_regs ms) 9%bv) by exact (HP3 9 ltac:(unfold acallee_saved; lia)).
  assert (S23' : getr regs3 23%bv = getr (ms_regs ms) 23%bv) by exact (HP3 23 ltac:(unfold acallee_saved; lia)).
  (* the bytes the copy kept *)
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - 112 - ESTACK <= a < spZ regs - 112) ->
    mbyte tfibsegs (mrestrict (w_H W2) mem3) a = mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a).
  { intros a Ha H1 H2. apply (mbyte_of_aview tfibsegs). apply HFR; [exact Ha | exact H1 | rewrite RT2; exact H2]. }
  assert (PR3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) by (intros a Ha; exact (HPR a (PR1 a Ha))).
  set (Er3 := Ereg regs3 (fs_extraT ++ pgt_xs E' res len c (d + n) buf cap)).
  assert (G2 : bv_unsigned (ew Er3 2) = spZ regs - 112)
    by (unfold Er3; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), S2'; exact RT2).
  assert (G8 : ew Er3 8 = Z_to_bv 64 o) by (unfold Er3; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), S8'; exact RT8).
  assert (G9 : ew Er3 9 = Z_to_bv 64 n) by (unfold Er3; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl), S9'; exact RT9).
  assert (G32 : ew Er3 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold Er3; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G33 : ew Er3 33 = Z_to_bv 64 res) by (unfold Er3; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G34 : ew Er3 34 = Z_to_bv 64 len) by (unfold Er3; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G35 : ew Er3 35 = Z_to_bv 64 c) by (unfold Er3; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G36 : ew Er3 36 = Z_to_bv 64 (d + n))
    by (unfold Er3; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G8u : bv_unsigned (ew Er3 8) = o) by (rewrite G8; apply wz; lia).
  assert (G9u : bv_unsigned (ew Er3 9) = n) by (rewrite G9; apply wz; lia).
  assert (G32u : bv_unsigned (ew Er3 32) = SHADOW_OFF) by (rewrite G32; apply wz; unfold SHADOW_OFF; lia).
  assert (G33u : bv_unsigned (ew Er3 33) = res) by (rewrite G33; apply wz; lia).
  assert (G34u : bv_unsigned (ew Er3 34) = len) by (rewrite G34; apply wz; lia).
  assert (G35u : bv_unsigned (ew Er3 35) = c) by (rewrite G35; apply wz; lia).
  assert (G36u : bv_unsigned (ew Er3 36) = d + n) by (rewrite G36; apply wz; unfold d in *; lia).
  (* a frame word / an o field of the call's state is the resume state's chunk *)
  assert (CMf : forall o0 (j : nat), ew Er3 j = ew Er j ->
    YP09.chunk_ok tfibsegs Er (mrestrict (w_H W2) (ms_mem ms)) (spZ regs - 112) (YP09.mkChunk o0 (CVal 8 (SOff j 0))) ->
    0 <= o0 -> o0 + 8 <= 112 ->
    YP09.chunk_ok tfibsegs Er3 (mrestrict (w_H W2) mem3) (spZ regs - 112) (YP09.mkChunk o0 (CVal 8 (SOff j 0)))).
  { intros o0 j Hj Hck Ho1 Ho2.
    apply (fsw_pf_chunk_move Er Er3 _ _ (spZ regs - 112) (spZ regs - 112) o0 o0 8 (SOff j 0) (SOff j 0) Hck).
    - rewrite !fsw_SOff0. exact Hj.
    - lia.
    - intros i Hi. cbn [Z.of_N] in Hi. apply KC; [lia | unfold d in *; lia | unfold ESTACK; lia]. }
  assert (CMo : forall off (w : N) e e', sv_denot Er3 e' = sv_denot Er e ->
    YP09.chunk_ok tfibsegs Er (mrestrict (w_H W2) (ms_mem ms)) o (YP09.mkChunk off (CVal w e)) ->
    0 <= off -> off + Z.of_N w <= 32 ->
    YP09.chunk_ok tfibsegs Er3 (mrestrict (w_H W2) mem3) o (YP09.mkChunk off (CVal w e'))).
  { intros off w e e' He Hck Ho1 Ho2.
    apply (fsw_pf_chunk_move Er Er3 _ _ o o off off w e e' Hck He); [lia|].
    intros i Hi. apply KC; [lia | unfold d in *; lia | unfold ESTACK; lia]. }
  (* the shadow-base cells on the memory after the copy (as FSW_put.v:985-1003) *)
  destruct (fsw_got_shadow B ly2 S2 W2 (unpoison U2 mem3) md3 (proj1 HSS) (proj2 HSS) (proj1 HARU3)) as [Kgot Kcell].
  assert (MBL : forall x, 0 <= x < SHADOW_OFF ->
    mbyte tfibsegs (mrestrict (w_H W2) mem3) x = mbyte tfibsegs (mrestrict (w_H W2) (unpoison U2 mem3)) x).
  { intros x Hx. unfold mbyte, mrestrict.
    rewrite (ARU_mem_low tfibsegs B ly2 S2 U2 W2 mem3 md3 (Z_to_bv 64 x) HARU3
      ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
    reflexivity. }
  assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
    val_mem tfibsegs (mrestrict (w_H W2) (unpoison U2 mem3)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem3) a 8 v).
  { intros a v Ha Hb Hv k0 Hk0. rewrite (MBL (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
  assert (Vgot : val_mem tfibsegs (mrestrict (w_H W2) mem3) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
    tfib_D_asan_shadow_memory_dynamic_address).
  { apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
    | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
    | exact (val_mem_of_rdword tfibsegs (w_H W2) (unpoison U2 mem3) _ _ Kgot)]. }
  assert (Vcell : val_mem tfibsegs (mrestrict (w_H W2) mem3) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
  { apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
    | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
    | exact (val_mem_of_rdword tfibsegs (w_H W2) (unpoison U2 mem3) _ _ Kcell)]. }
  (* the end of the new text is a byte of the new block: present after the copy *)
  assert (PZ : apresent (w_H W2) mem3 (d + n)).
  { destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U2 mem3) md3 (res - HEAD) (c + HEAD) (proj1 HARU3) Hin)
      as (_ & _ & _ & _ & Hbp & _).
    destruct (Hbp (d + n) ltac:(rewrite RQB; unfold HEAD, d in *; lia)) as ((Hh & b & Hb) & _).
    split; [exact Hh|]. exists b.
    rewrite <- (fsw_pf_unp B ly2 S2 U2 W2 mem3 md3 (d + n) HARU3);
      [exact Hb | unfold d in *; lia | unfold d, SHADOW_OFF in *; lia]. }
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  (* the end of the new text is a buffer byte, so no image byte: off the two shadow-base cells *)
  assert (ZG : d + n + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/
               tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= d + n).
  { destruct (Z_le_gt_dec (d + n + 1) tfib_D_GOT_asan_shadow_memory_dynamic_address); [left; lia|].
    destruct (Z_le_gt_dec (tfib_D_GOT_asan_shadow_memory_dynamic_address + 8) (d + n)); [right; lia|].
    exfalso. apply (BNI (d + n)); [unfold d in *; lia|]. apply fsw_pf_in_img.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address in *; lia. }
  assert (ZC : d + n + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/
               tfib_D_asan_shadow_memory_dynamic_address + 8 <= d + n).
  { destruct (Z_le_gt_dec (d + n + 1) tfib_D_asan_shadow_memory_dynamic_address); [left; lia|].
    destruct (Z_le_gt_dec (tfib_D_asan_shadow_memory_dynamic_address + 8) (d + n)); [right; lia|].
    exfalso. apply (BNI (d + n)); [unfold d in *; lia|]. apply fsw_pf_in_img.
    unfold tfib_D_asan_shadow_memory_dynamic_address in *; lia. }
  assert (HSR0 : st_ok tfibsegs Er3
      (mkSS 541364 sr_atoms (fsT_ret_regions 112 fsw_pf_cs [fsw_pf_o2; fsw_pf_z2]) None
        (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: fsw_pf_gf2) []
           fsw_pf_al2))
      (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 541364) mem3 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); fold Er3.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - unfold fsT_ret_regions. cbn [app].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      + (* the frame, its 13 saved words *)
        unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite G2. split; [lia|]. split; [lia|]. split.
        * intros q Hq. apply (apresent_writable tfibsegs).
          apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem3 md3 _ HARU3); [lia|]. apply Hpres3. lia.
        * unfold fsw_pf_cs. repeat constructor.
          all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o2 (CVal 8 (SOff ?j 0))) =>
            exact (CMf o2 j eq_refl (HCF (YP09.mkChunk o2 (CVal 8 (SOff j 0)))
                     ltac:(repeat (first [left; reflexivity | right]))) ltac:(lia) ltac:(lia))
          end.
      + (* the GOT word of the shadow base *)
        unfold fs_got_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
        split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros q Hq; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
          (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
          [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
      + (* the shadow-base cell *)
        unfold fs_bcell_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
        split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros q Hq; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
          [rewrite fsw_SOff0, G32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
      + (* o: buf = res, len, cap = c, failed = 0, as run 1 stored them; its length field writable *)
        unfold fsw_pf_o2, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite G8u. split; [lia|]. split; [lia|]. split.
        { intros q Hq. apply (apresent_writable tfibsegs).
          apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem3 md3 _ HARU3); [lia|]. apply Hpres3. lia. }
        constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
        * exact (CMo 0 8%N (SOff 10 0) (SOff 33 0) ltac:(rewrite !fsw_SOff0, G33, F10; reflexivity)
                   (HCO1 (YP09.mkChunk 0 (CVal 8 (SOff 10 0))) ltac:(repeat (first [left; reflexivity | right])))
                   ltac:(lia) ltac:(cbn [Z.of_N]; lia)).
        * exact (CMo 8 8%N (SOff 34 0) (SOff 34 0) ltac:(rewrite !fsw_SOff0, G34, F34; reflexivity)
                   (HCO1 (YP09.mkChunk 8 (CVal 8 (SOff 34 0))) ltac:(repeat (first [left; reflexivity | right])))
                   ltac:(lia) ltac:(cbn [Z.of_N]; lia)).
        * exact (CMo 16 8%N (SOff 35 0) (SOff 35 0) ltac:(reflexivity)
                   (HCO1 (YP09.mkChunk 16 (CVal 8 (SOff 35 0))) ltac:(repeat (first [left; reflexivity | right])))
                   ltac:(lia) ltac:(cbn [Z.of_N]; lia)).
        * exact (CMo 24 4%N (SLit 0) (SLit 0) ltac:(reflexivity)
                   (HCO1 (YP09.mkChunk 24 (CVal 4 (SLit 0))) ltac:(repeat (first [left; reflexivity | right])))
                   ltac:(lia) ltac:(cbn [Z.of_N]; lia)).
      + (* the byte after the new text, writable *)
        unfold fsw_pf_z2, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite G36u. split; [unfold d in *; lia|]. split; [unfold d in *; lia|]. split; [|constructor].
        intros q Hq. replace (d + n + q) with (d + n) by lia. apply (apresent_writable tfibsegs). exact PZ.
    - apply pairwise_disjoint_of_extents.
      unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, fsw_pf_o2, fsw_pf_z2, extent_of_region.
      cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite G2, G8u, G36u.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
      unfold d in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok fsw_pf_gf2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite G2, G32u, G8u, G33u, G34u, G35u, G9u, G36u. unfold fsw_pf_CEIL.
        change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        unfold d in *. repeat split; lia.
      + cbn [f_alias alias_ok fsw_pf_al2]. split; [|exact I].
        apply U_inj. rewrite !U_SAlu, (U_atom Er3 9 n G9), (U_atom Er3 33 res G33), (U_atom Er3 34 len G34),
          (U_atom Er3 36 (d + n) G36) by (unfold d in *; lia).
        cbn [zalu_raw]. rewrite (zcanon_id (n + res)) by (unfold M64; lia).
        rewrite zcanon_id by (unfold M64; lia). unfold d. lia. }
  assert (HSR : st_ok tfibsegs Er3 fsw_pf_ssr (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 541364) mem3 (seg_rom tfibsegs)))).
  { refine (st_ok_set_reg tfibsegs Er3 _ _ 23%bv (SOff 32 0) HSR0 _ _).
    - intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
    - change (ms_regs (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 541364) mem3 (seg_rom tfibsegs)))) with regs3.
      rewrite fsw_SOff0, G32, S23'. exact RT23. }
  clear HSR0.
  assert (SHOK2 : sh_ok tfibsegs fs_Bx fsw_pf_SH2 Er3 (mrestrict (w_H W2) mem3)).
  { unfold fsw_pf_SH2. constructor; [|constructor; [|constructor]].
    - apply (shent_ok_of_range tfibsegs (w_H W2) mem3 Er3 fs_Bx 8%nat o 32 o 0 32 (RAO mem3 md3 HARU3)).
      + unfold fs_Bx. apply (U_atom Er3 32 SHADOW_OFF G32). unfold SHADOW_OFF; lia.
      + apply (U_atom Er3 8 o G8). lia.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF. lia.
    - assert (HRAz : range_addressable (aview tfibsegs (w_H W2) mem3) SHADOW_OFF (d + n) 1).
      { apply (fsw_pf_ra_raw (w_H W2) U2 mem3 (d + n) 1); [unfold d in *; lia | unfold d in *; lia | |].
        - intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU3))); [unfold d in *; lia|].
          exact (fsw_pf_heads_out B ly2 S2 U2 W2 (unpoison U2 mem3) md3 res c x (proj1 HARU3) FH2 Hin Hc0
                   ltac:(unfold d in *; lia)).
        - apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem3) md3 (res - HEAD) (c + HEAD)
            (d + n) 1 (proj1 HARU3) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
      apply (shent_ok_of_range tfibsegs (w_H W2) mem3 Er3 fs_Bx 36%nat (d + n) 1 (d + n) 0 1 HRAz).
      + unfold fs_Bx. apply (U_atom Er3 32 SHADOW_OFF G32). unfold SHADOW_OFF; lia.
      + apply (U_atom Er3 36 (d + n) G36). unfold d in *; lia.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF, d in *. lia. }
  (* run 3 (the fast arm's): the length store o + 8, the 0 after the new text, the epilogue, to the ret 0x84314 *)
  fsw_aj_run_tokU fsw_wr_tbl_ok HSR HJ3 HARU3 SHOK2 fs_Bspan.
  + lazymatch goal with |- context C [ss_mem ?ssx] =>
      let rs' := eval vm_compute in (ss_mem ssx) in
      let g := context C [rs'] in change g end.
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
      [reflexivity | rewrite G2; lia | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
      [reflexivity | rewrite G8u; lia | cbn; lia | cbn; lia |].
    eapply awr_ok_cons_gen with (k := 36%nat) (b := d + n); [reflexivity | exact G36u | | apply awr_ok_nil].
    intros a Ha. cbn in Ha. left. right. right. left.
    exists (res - HEAD), (c + HEAD). split; [exact Hin|]. split; [exact HNEW|]. rewrite RQB. unfold d, HEAD in *. lia.
  + (* the run wrote only the frame, o's length field and the 0 after the new text *)
    rename ms0 into msf.
    assert (MF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o + 8 <= a < o + 16) ->
      a <> d + n -> ms_mem msf (Z_to_bv 64 a) = mem3 (Z_to_bv 64 a)).
    { intros a Ha H1 H2 H3. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
      vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?G2, ?G8u, ?G36u in Hr; lia. }
    pose proof (fun a Ha => apresent_grows _ _ _ a HG (PR3 a Ha)) as PRF.
    lazymatch type of HSR with st_ok _ ?Ef _ _ => assert (HAG : env_agree 50 Er3 Ef) end.
    { lazymatch goal with |- env_agree _ _ (ewset (ewset _ _ ?w1) _ ?w2) => exact (env_agree_extK Er3 50 [w1; w2]) end. }
    assert (FR1 : getr (ms_regs msf) 1%bv = getr regs 1%bv).
    { pf_reg HSR. rewrite (sv_denot_agree 50 Er3 _ (SOff 37 0) HAG eq_refl). rewrite fsw_SOff0.
      change (ew Er3 37) with (ew E' 1). apply pgt_E'_reg; [lia | reflexivity]. }
    (* o's fields and the 0 after the new text, read off the final state *)
    pose proof (st_ok_mem_ok tfibsegs _ _ _ HSR) as (_ & HRSF & _).
    cbn [ms_mem restrict ss_mem] in HRSF.
    apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in HRSF.
    pose proof (Forall_inv HRSF) as RO. apply Forall_inv_tail, Forall_inv in HRSF. rename HRSF into RZ.
    destruct RO as (_ & _ & _ & HCO). cbn [YP09.r_base YP09.r_chunks base_val] in HCO.
    rewrite (proj1 HAG 8%nat ltac:(lia)), G8u in HCO.
    destruct RZ as (_ & _ & _ & HCZ). cbn [YP09.r_base YP09.r_chunks base_val] in HCZ.
    rewrite (proj1 HAG 36%nat ltac:(lia)), G36u in HCZ. apply Forall_inv in HCZ.
    assert (VLEN : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (o + 8) 8 (len + n)).
    { apply (val_of_chunk_ok tfibsegs _ _ o 8 8 _ (len + n) (Forall_inv HCO)).
      - lazymatch goal with |- context [sv_denot ?Ef ?e] => lazymatch Ef with Er3 => fail | _ =>
          rewrite (sv_denot_agree 50 Er3 Ef e HAG eq_refl) end end.
        rewrite denot_lit_U. f_equal.
        rewrite U_SAlu, (U_atom Er3 9 n G9), (U_atom Er3 34 len G34) by lia. cbn [zalu_raw].
        rewrite zcanon_id by (unfold M64; lia). lia.
      - cbn [Z.of_N]. lia.
      - cbn [Z.of_N]. lia. }
    rewrite Forall_forall in HCO.
    assert (VBUF : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (o + 0) 8 res).
    { apply (val_of_chunk_ok tfibsegs _ _ o 0 8 (SOff 33 0) res
        (HCO (YP09.mkChunk 0 (CVal 8 (SOff 33 0))) ltac:(repeat (first [left; reflexivity | right])))).
      - rewrite (sv_denot_agree 50 Er3 _ (SOff 33 0) HAG eq_refl), fsw_SOff0. exact G33.
      - cbn [Z.of_N]. lia.
      - cbn [Z.of_N]. lia. }
    assert (VCAP : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (o + 16) 8 c).
    { apply (val_of_chunk_ok tfibsegs _ _ o 16 8 (SOff 35 0) c
        (HCO (YP09.mkChunk 16 (CVal 8 (SOff 35 0))) ltac:(repeat (first [left; reflexivity | right])))).
      - rewrite (sv_denot_agree 50 Er3 _ (SOff 35 0) HAG eq_refl), fsw_SOff0. exact G35.
      - cbn [Z.of_N]. lia.
      - cbn [Z.of_N]. lia. }
    assert (VFAIL : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (o + 24) 4 0).
    { apply (val_of_chunk_ok tfibsegs _ _ o 24 4 (SLit 0) 0
        (HCO (YP09.mkChunk 24 (CVal 4 (SLit 0))) ltac:(repeat (first [left; reflexivity | right]))));
        [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
    assert (VZ : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (d + n + 0) 1 0).
    { apply (val_of_chunk_ok tfibsegs _ _ (d + n) 0 1 (SLit 0) 0 HCZ); [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
    (* every other byte: kept, against the memory after fuzz_realloc and against put's entry *)
    assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o + 8 <= a < o + 16) ->
      a <> d + n -> mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msf)) a = mbyte tfibsegs (mrestrict (w_H W2) mem3) a)
      by (intros a H0 H1 H2 H3; unfold mbyte, mrestrict; rewrite (MF a H0 H1 H2 H3); reflexivity).
    assert (KH : forall a, spZ regs <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
      mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msf)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
    { intros a Ha Ho. rewrite (KF a) by (unfold d in *; lia). rewrite (KC a) by (unfold ESTACK, d in *; lia).
      rewrite (K1 a) by lia. exact (KEEPE a Ha). }
    assert (KL : forall a, 0 <= a < alloc_ceiling -> ~ (d <= a < d + n + 1) ->
      mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msf)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a).
    { intros a Ha Hd. rewrite (KF a) by (unfold d in *; lia). rewrite (KC a) by (unfold ESTACK, d in *; lia).
      apply K1; lia. }
    assert (VL2 : forall a k v, 0 <= a -> a + Z.of_nat k <= alloc_ceiling ->
      (forall i, 0 <= i < Z.of_nat k -> ~ (d <= a + i < d + n + 1)) ->
      val_mem tfibsegs (mrestrict (w_H W2) mem2) a k v -> val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) a k v).
    { intros a k v Ha Hk Ho Hv i Hi. rewrite (KL (a + Z.of_nat i) ltac:(lia) (Ho (Z.of_nat i) ltac:(lia))). exact (Hv i Hi). }
    (* the return *)
    eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok).
    * exact HSR.
    * vm_compute; reflexivity.
    * vm_compute; reflexivity.
    * rewrite FR1. exact Hra.
    * eapply ajournal_mono_k; [exact HJ3 | exact HKK].
    * exact HARU3.
    * lazymatch type of HSR with
      | st_ok _ ?Ef ?ssf _ =>
        apply (fsw_preserved (w_H W2) Ef ssf _ regs (fun r : bv 5 => sr_get (ss_regs ssf) r) HSR);
        [vm_compute; reflexivity|];
        let r := fresh "r" in let Hr := fresh "Hr" in
        intros r Hr; cbv [CALLEE_SAVED In] in Hr;
        repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
      end;
      cbv beta;
      lazymatch goal with
      | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
      end;
      lazymatch goal with |- context [sv_denot ?Ef ?e] => lazymatch Ef with Er3 => fail | _ =>
        rewrite (sv_denot_agree 50 Er3 Ef e HAG eq_refl) end end;
      first
      [ rewrite denot_lit_U, U_SOff, G2, zcanon_id by (unfold M64; lia);
        replace (spZ regs - 112 + 112) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
      | rewrite fsw_SOff0; unfold Er3; rewrite (ew_Ereg_nat regs3 _ 3 3%bv eq_refl), S3'; exact RT3
      | rewrite fsw_SOff0; unfold Er3; rewrite (ew_Ereg_nat regs3 _ 4 4%bv eq_refl), S4'; exact RT4
      | lazymatch goal with |- sv_denot _ (SOff ?j 0) = _ =>
          let k := eval vm_compute in (if Nat.eqb j 37 then 1%nat else if Nat.eqb j 38 then 8%nat
                                       else if Nat.eqb j 39 then 9%nat else (j - 22)%nat) in
          rewrite fsw_SOff0; change (ew Er3 j) with (ew E' k); apply pgt_E'_reg; [lia | vm_compute; reflexivity]
        end ].
    * intros matq.
      split; [reflexivity|]. split; [reflexivity|].
      split.
      { unfold wout_ok. split; [exact Ho8|]. split; [exact Ho0|]. split; [lia|]. split.
        { intros i Hi.
          assert (Hp : apresent (w_H W2) mem2 (o + i)).
          { apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem2 md2 _ HARU2m); [lia|]. apply Hpres2. lia. }
          pose proof (PRF _ Hp) as Hp'. split; [exact (apresent_writable tfibsegs _ _ _ Hp') | exact Hp']. }
        split; [lia|]. split; [lia|].
        split; [rewrite Z.add_0_r in VBUF; exact VBUF|].
        split; [rewrite length_app, Nat2Z.inj_add; fold len; rewrite Hlen; exact VLEN|].
        split; [exact VCAP|]. split; [exact VFAIL|].
        split; [left; reflexivity|].
        split; [unfold WriterSpec.bytes_ok in *; apply Forall_app; split; assumption|].
        right. split; [exact Hcj|]. split; [|split].
        - unfold fs_rblock. split; [exact Hin|]. split; [exact Hb16|]. split; [exact Hc0|].
          apply (VL2 (res - HEAD) 8%nat c); [unfold HEAD; lia | unfold HEAD; lia
            | intros i Hi; unfold d, HEAD in *; lia | exact Vhead].
        - rewrite length_app, Nat2Z.inj_add. fold len. lia.
        - unfold zbytes_at in HTXT, HZS2 |- *. intros j Hjl. rewrite !length_app in Hjl. cbn [length] in Hjl.
          destruct (Nat.lt_ge_cases j (length text)) as [Hj1|Hj1].
          + rewrite <- app_assoc, app_nth1 by exact Hj1.
            destruct (HTXT j Hj1) as (Hv & Hr).
            split; [|exact Hr].
            apply (VL2 (res + Z.of_nat j) 1%nat); [lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold d, len in *; lia
              | intros i Hi; cbn [Z.of_nat Pos.of_succ_nat] in Hi; unfold d, len in *; lia | exact Hv].
          + destruct (Nat.lt_ge_cases j (length text + length bs)) as [Hj2|Hj2].
            * rewrite <- app_assoc, app_nth2 by exact Hj1. rewrite app_nth1 by lia.
              destruct (HZS2 (j - length text)%nat ltac:(lia)) as (Hv & Hr). split; [|exact Hr].
              intros k Hk. assert (k = 0%nat) by lia. subst k. specialize (Hv 0%nat Hk). rewrite <- Hv.
              replace (res + Z.of_nat j + Z.of_nat 0) with (d + Z.of_nat (j - length text)) by (unfold d, len; lia).
              replace (s + Z.of_nat (j - length text) + Z.of_nat 0) with (s + Z.of_nat (j - length text)) by lia.
              rewrite (KF (d + Z.of_nat (j - length text))) by (unfold d, len in *; lia).
              rewrite (fsw_pf_mbyte_aview2 (w_H W2) (ms_mem ms) mem3 _ _ (HCP (Z.of_nat (j - length text)) ltac:(lia))).
              unfold mbyte, mrestrict. rewrite (LOWT (s + Z.of_nat (j - length text))) by lia. reflexivity.
            * assert (Ej : j = (length text + length bs)%nat) by lia. subst j.
              rewrite <- app_assoc, app_nth2 by lia. rewrite app_nth2 by lia.
              replace (length text + length bs - length text - length bs)%nat with 0%nat by lia. cbn [nth].
              split; [|lia].
              replace (res + Z.of_nat (length text + length bs)) with (d + n + 0) by (unfold d, len; lia). exact VZ. }
      split.
      { intros a Ha Hno. split; [apply KH; lia|].
        split; intros _.
        - apply (apresent_writable tfibsegs). apply PRF.
          apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem2 md2 _ HARU2m); [lia|]. apply Hpres2. lia.
        - apply (apresent_writable tfibsegs). apply HPRESENT. lia. }
      split.
      { assert (GI : forall g v, 0x10000 <= g -> g + 8 <= 0x5fd000 ->
          val_mem tfibsegs (mrestrict (w_H W2) mem2) g 8 v -> val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) g 8 v).
        { intros g v Hg1 Hg2 Hv. apply VL2; [lia | lia | | exact Hv].
          intros i Hi Hx. apply (BNI (g + i)); [unfold d in *; lia|]. apply fsw_pf_in_img. lia. }
        unfold fs_glob, fs_glob_at in HGLOB2 |- *. destruct HGLOB2 as (GL1 & GL2 & GL3 & GL4 & GR).
        split; [apply GI; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact GL1]|].
        split; [apply GI; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact GL2]|].
        split; [apply GI; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact GL3]|].
        split; [apply GI; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact GL4]|].
        exact GR. }
      intros i Hi. rewrite <- (SKEEP i Hi). apply KL; [lia|]. intros Hx. apply (SDISJ (s + i)); [lia | unfold d, HEAD in *; lia].
Qed.

(* ================= piece 4: THE REFUSED TAIL ================= *)
(* fuzz_realloc answered NULL (its cnt = fail arm: heads U kept, blocks unchanged, journal 0). From the resume state
   `beqz a0` is taken: put stores 1 into o->failed (4 bytes at o + 24) and returns (MEASURED: the run stops at the ret
   541460 = 0x84314, sh_obls = []). o's buf / len / cap fields are read back off the resume state's chunks (atoms 50,
   34, 51), the buffer's facts off the memory after the call. *)
Lemma pgt_refused : forall kc ly2 S2 W2 regs2 mem2 md2 d K,
  ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U mem2) md2 kc ->
  ARU tfibsegs B ly2 S2 U W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pgt_xs E' 0 (Z.of_nat (length text)) c d buf cap)) pgt_ss1
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 541288) mem2 (seg_rom tfibsegs))) ->
  aregs_preserved (ms_regs ms') regs2 ->
  getr regs2 10%bv = w64 0 ->
  (forall a, spZ regs <= a < 2 ^ 64 ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a) ->
  ((cap = 0 /\ buf = 0 /\ text = []) \/
   ((exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ fs_rblock tfibsegs B ly2 S2 W2 mem2 buf cap /\
    Z.of_nat (length text) < cap /\ zbytes_at tfibsegs W2 mem2 buf (text ++ [0]))) ->
  (forall i, 0 <= i < n ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)) ->
  fs_glob tfibsegs W2 mem2 live peak (cnt + 1) SIZE_MAXZ ->
  kc <= K ->
  SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 541288) mem2 (seg_rom tfibsegs)) md2)
    (fpostU tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md K U
      (fun ly' S' W' regs' mem' md' =>
         ly' = ly2 /\ S' = S2 /\
         wout_ok B tfibsegs ly' S' W' mem' o buf cap 1 text /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
         fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ /\
         (forall i, 0 <= i < n ->
            mbyte tfibsegs (mrestrict (w_H W') mem') (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)))).
Proof.
intros kc ly2 S2 W2 regs2 mem2 md2 d K HJ2 HARU2 HS1 HP R10 KEEPE HCASE2 SKEEP HGLOB2 HKK.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTKa & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HARU2 as HARU2m.
pose proof HSRC as (Hs0 & Hsn).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
destruct pgt_call_regs as (Ems & R1 & R2 & R3 & R4 & R8 & R9 & R10c & R11 & R18 & R22 & R23 & R19 & R20 & R21 &
  R24 & R25 & R26 & R27).
set (len := Z.of_nat (length text)) in *.
assert (Hlen0 : 0 <= len) by (unfold len; lia).
assert (Hn0 : 0 <= n) by lia.
unfold WMAX in HWM, HCAP, HcW.
set (Er := Ereg regs2 (fs_extraT ++ pgt_xs E' 0 len c d buf cap)) in *.
assert (P2 : getr regs2 2%bv = getr (ms_regs ms') 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr (ms_regs ms') 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr (ms_regs ms') 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr (ms_regs ms') 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (F2 : bv_unsigned (ew Er 2) = spZ regs - 112)
  by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; exact R2).
assert (F3 : ew Er 3 = getr regs 3%bv) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl), P3; exact R3).
assert (F4 : ew Er 4 = getr regs 4%bv) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl), P4; exact R4).
assert (F8 : ew Er 8 = Z_to_bv 64 o) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8; exact R8).
assert (F10 : ew Er 10 = Z_to_bv 64 0) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact R10).
assert (F32 : ew Er 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold Er; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F34 : ew Er 34 = Z_to_bv 64 len) by (unfold Er; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F50 : ew Er 50 = Z_to_bv 64 buf)
  by (unfold Er; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F51 : ew Er 51 = Z_to_bv 64 cap)
  by (unfold Er; change 51%nat with (32 + 19)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F8u : bv_unsigned (ew Er 8) = o) by (rewrite F8; apply wz; lia).
(* o's 32 bytes addressable over U at ly2 (as in pgt_granted) *)
assert (HLO2 : layout_ok ly2) by exact (am_layout _ _ _ _ (proj1 (proj1 HARU2))).
pose proof (lo_top ly2 HLO2) as LTOP.
assert (Hlo8 : ly_stk_lo ly2 mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & L5 & _). unfold page_aligned in L5.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L5]]. }
assert (Hhi8 : ly_stk_hi ly2 mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & _ & L6 & _). unfold page_aligned in L6.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L6]]. }
assert (HRA32 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF o 32).
{ assert (HZS0 : zero_shadow (aview tfibsegs (w_H W2) (unpoison U mem2)) SHADOW_OFF
                  (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2)).
  { exact (al_zshadow _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2
             (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2) (proj1 HARU2) (or_introl eq_refl)). }
  apply (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly2 S2 U W2 mem2 md2 (w_H W2) o 32 HARU2 ltac:(lia) ltac:(lia))).
  eapply range_addressable_sub;
    [ apply (zero_shadow_range (aview tfibsegs (w_H W2) (unpoison U mem2)) SHADOW_OFF
               (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2) Hlo8
               ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS0)
    | lia | lia]. }
assert (SHOK1 : sh_ok tfibsegs fs_Bx pgt_SH1 Er (mrestrict (w_H W2) mem2)).
{ unfold pgt_SH1. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W2) mem2 Er fs_Bx 8%nat o 32 o 0 32 HRA32).
  - unfold fs_Bx. apply (U_atom Er 32 SHADOW_OFF F32). unfold SHADOW_OFF; lia.
  - apply (U_atom Er 8 o F8). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. lia. }
(* `beqz a0`: a0 = 0, taken *)
srr_branch_tok fsw_wr_tbl_ok HS1 SHOK1 fs_Bspan.
2: { exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom Er 10 0 F10) in Hc by lia.
     assert (U0 : YP0e.U Er (SLit 0) = 0) by reflexivity. rewrite U0 in Hc. cbn in Hc. discriminate Hc. }
(* the run: o->failed = 1, the epilogue, to the ret 0x84314 *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS1 HJ2 HARU2 SHOK1 fs_Bspan.
- lazymatch goal with |- context C [ss_mem ?ssx] =>
    let rs' := eval vm_compute in (ss_mem ssx) in
    let g := context C [rs'] in change g end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
    [reflexivity | rewrite F2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
    [reflexivity | rewrite F8u; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil.
- assert (MF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
    ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { intros a Ha H1 H2. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
    vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?F2, ?F8u in Hr; lia. }
  pose proof (fun a => apresent_grows _ _ _ a HG) as PRF.
  assert (FR1 : getr (ms_regs ms) 1%bv = getr regs 1%bv).
  { pf_reg HS1. rewrite fsw_SOff0. change (ew Er 37) with (ew E' 1). apply pgt_E'_reg; [lia | reflexivity]. }
  (* o's fields, read off the final state *)
  pose proof (st_ok_mem_ok tfibsegs _ _ _ HS1) as (_ & HRSF & _).
  cbn [ms_mem restrict ss_mem] in HRSF.
  apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv in HRSF.
  destruct HRSF as (_ & _ & _ & HCO). cbn [YP09.r_base YP09.r_chunks base_val] in HCO.
  rewrite F8u in HCO. rewrite Forall_forall in HCO.
  assert (VB : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (o + 0) 8 buf).
  { apply (val_of_chunk_ok tfibsegs _ _ o 0 8 (SOff 50 0) buf
      (HCO (YP09.mkChunk 0 (CVal 8 (SOff 50 0))) ltac:(repeat (first [left; reflexivity | right]))));
      [rewrite fsw_SOff0; exact F50 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
  assert (VL : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (o + 8) 8 len).
  { apply (val_of_chunk_ok tfibsegs _ _ o 8 8 (SOff 34 0) len
      (HCO (YP09.mkChunk 8 (CVal 8 (SOff 34 0))) ltac:(repeat (first [left; reflexivity | right]))));
      [rewrite fsw_SOff0; exact F34 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
  assert (VC : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (o + 16) 8 cap).
  { apply (val_of_chunk_ok tfibsegs _ _ o 16 8 (SOff 51 0) cap
      (HCO (YP09.mkChunk 16 (CVal 8 (SOff 51 0))) ltac:(repeat (first [left; reflexivity | right]))));
      [rewrite fsw_SOff0; exact F51 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
  assert (VF : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (o + 24) 4 1).
  { apply (val_of_chunk_ok tfibsegs _ _ o 24 4 (SLit 1) 1
      (HCO (YP09.mkChunk 24 (CVal 4 (SLit 1))) ltac:(repeat (first [left; reflexivity | right]))));
      [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
  (* every other byte: kept *)
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a)
    by (intros a H0 H1 H2; unfold mbyte, mrestrict; rewrite (MF a H0 H1 H2); reflexivity).
  assert (KH : forall a, spZ regs <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a)
    by (intros a Ha Ho; rewrite (KF a) by lia; exact (KEEPE a Ha)).
  assert (KL : forall a, 0 <= a < alloc_ceiling ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a)
    by (intros a Ha; apply KF; lia).
  assert (VL2 : forall a k v, 0 <= a -> a + Z.of_nat k <= alloc_ceiling ->
    val_mem tfibsegs (mrestrict (w_H W2) mem2) a k v -> val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a k v)
    by (intros a k v Ha Hk Hv i Hi; rewrite (KL (a + Z.of_nat i) ltac:(lia)); exact (Hv i Hi)).
  (* the return *)
  eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok).
  + exact HS1.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + rewrite FR1. exact Hra.
  + eapply ajournal_mono_k; [exact HJ2 | exact HKK].
  + exact HARU2.
  + lazymatch type of HS1 with
    | st_ok _ ?Ef ?ssf _ =>
      apply (fsw_preserved (w_H W2) Ef ssf _ regs (fun r : bv 5 => sr_get (ss_regs ssf) r) HS1);
      [vm_compute; reflexivity|];
      let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; cbv [CALLEE_SAVED In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
    end;
    cbv beta;
    lazymatch goal with
    | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
    end;
    first
    [ rewrite denot_lit_U, U_SOff, F2, zcanon_id by (unfold M64; lia);
      replace (spZ regs - 112 + 112) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
    | rewrite fsw_SOff0; exact F3
    | rewrite fsw_SOff0; exact F4
    | lazymatch goal with |- sv_denot _ (SOff ?j 0) = _ =>
        let k := eval vm_compute in (if Nat.eqb j 37 then 1%nat else if Nat.eqb j 38 then 8%nat
                                     else if Nat.eqb j 39 then 9%nat else (j - 22)%nat) in
        rewrite fsw_SOff0; change (ew Er j) with (ew E' k); apply pgt_E'_reg; [lia | vm_compute; reflexivity]
      end ].
  + intros matq.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold wout_ok. split; [exact Ho8|]. split; [exact Ho0|]. split; [lia|]. split.
      { intros i Hi.
        assert (Hp : apresent (w_H W2) mem2 (o + i)).
        { apply (fsw_apresent_unpoison B ly2 S2 U W2 mem2 md2 _ HARU2m); [lia|]. apply Hpres2. lia. }
        pose proof (PRF _ Hp) as Hp'. split; [exact (apresent_writable tfibsegs _ _ _ Hp') | exact Hp']. }
      split; [exact Hbuf64|]. split; [exact Hcap64|].
      split; [rewrite Z.add_0_r in VB; exact VB|].
      split; [exact VL|]. split; [exact VC|]. split; [exact VF|].
      split; [right; reflexivity|]. split; [exact Htok|].
      destruct HCASE2 as [Hz | (Hj & HRB2 & Hlt & HZB2)]; [left; exact Hz | right].
      pose proof HRB2 as (Hin2 & Hb16 & Hc0 & Vhead).
      destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 (buf - HEAD) (cap + HEAD) (proj1 HARU2m) Hin2)
        as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
      pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2).
      split; [exact Hj|]. split; [|split; [exact Hlt|]].
      - unfold fs_rblock. split; [exact Hin2|]. split; [exact Hb16|]. split; [exact Hc0|].
        apply (VL2 (buf - HEAD) 8%nat cap); [unfold HEAD in *; lia | unfold HEAD in *; lia | exact Vhead].
      - unfold zbytes_at in HZB2 |- *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) HZB2).
        intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KL. unfold HEAD in *. lia. }
    split.
    { intros a Ha Hno. split; [apply KH; lia|].
      split; intros _.
      - apply (apresent_writable tfibsegs). apply PRF.
        apply (fsw_apresent_unpoison B ly2 S2 U W2 mem2 md2 _ HARU2m); [lia|]. apply Hpres2. lia.
      - apply (apresent_writable tfibsegs). apply HPRESENT. lia. }
    split.
    { unfold fs_glob, fs_glob_at in HGLOB2 |- *. destruct HGLOB2 as (GL1 & GL2 & GL3 & GL4 & GR).
      split; [apply VL2; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact GL1]|].
      split; [apply VL2; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact GL2]|].
      split; [apply VL2; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact GL3]|].
      split; [apply VL2; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact GL4]|].
      exact GR. }
    intros i Hi. rewrite <- (SKEEP i Hi). apply KL. lia.
Qed.

(* ================= the composition ================= *)
(* put1 on the grow arm (WriterApp.v put1: failed = 0, need = len + n + 1 > cap, newcap cap need = c) *)
Lemma pgt_put1 : WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs =
  if cnt =? fail then WriterApp.mkW 1 text cap ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1) [c]
  else WriterApp.mkW 0 (text ++ bs) c ((cnt + 1) mod 2 ^ 64) fail [c].
Proof.
unfold WriterApp.put1.
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls negb Z.eqb].
rewrite Hlen. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite <- Hcnew. reflexivity.
Qed.

(* the source range after fuzz_realloc, from wsrc_kept: in a live block other than the old buffer (its bytes off the
   callee's footprint FP1, kept by the callee journal; its user bytes hold no head after the call), or a prefix of a
   read-only literal (fs_img_facts' cstr_ok, read on the memory after the call through FSW_rd.arodata_kept); and it
   avoids every block the call created *)
Lemma pgt_src_after : forall FP1 kc ly2 S2 U2 W2 mem2 md2,
  ajournal tfibsegs B STK_fuzz_realloc (spZ (ms_regs ms')) FP1 ly S W (unpoison U (ms_mem ms')) mdc []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 -> fs_heads B ly2 S2 U2 ->
  (forall a, inFP FP1 a -> inFP FS_PSTAT_FP a \/ (cap <> 0 /\ buf - HEAD <= a < buf + cap)) ->
  (forall p k, In (p, k) (ablocks B ly S) -> p <> buf - HEAD -> In (p, k) (ablocks B ly2 S2)) ->
  (forall r, In r U2 -> In r U \/ exists m, In (fst r, m) (ablocks B ly2 S2) /\ ~ In (fst r, m) (ablocks B ly S) /\
     snd r = HEAD /\ HEAD <= req_size m) ->
  zbytes_at tfibsegs W2 mem2 s bs /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF s n /\
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) mem2) s n) /\ amem_range s n /\
  (forall i, 0 <= i < n ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)) /\
  (forall q m, In (q, m) (ablocks B ly2 S2) -> ~ In (q, m) (ablocks B ly S) -> 0 < m ->
     forall x, s <= x < s + n -> ~ (q <= x < q + req_size m)).
Proof.
intros FP1 kc ly2 S2 U2 W2 mem2 md2 HJc HARU2 FH2 HFP1 HBK HU2.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & _).
pose proof HSRC as (Hs0 & Hsn).
pose proof HOUT as (_ & _ & _ & _ & Hbuf64 & Hcap64 & _ & _ & _ & _ & _ & _ & Hcase).
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (SB : same_below mem (ms_mem ms') alloc_ceiling) by (intros x Hx; apply HMF; lia).
(* the old buffer, a block of the entry when cap <> 0 *)
assert (OLDB : cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S) /\ 0 < cap).
{ intros Hc0. destruct Hcase as [(E0 & _) | (_ & (Hin & _ & Hcp & _) & _)]; [lia | split; [exact Hin | exact Hcp]]. }
(* a byte of a block live at both ends, off FP1, is the entry's *)
assert (BK : forall p k i, In (p, k) (ablocks B ly S) -> In (p, k) (ablocks B ly2 S2) -> 0 <= i < req_size k ->
  ~ inFP FP1 (p + i) ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) (p + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (p + i)).
{ intros p k i H1 H2 Hi Hnf.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p k HAR H1) as (_ & Hp4096 & Hpc & Hpapp & _).
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Hpapp.
  rewrite <- (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling (p + i) SB) by lia.
  apply (mbyte_of_aview tfibsegs).
  rewrite <- (aview_at tfibsegs (w_H W2) (unpoison U2 mem2) mem2 (p + i))
    by (apply (fsw_pf_unp B ly2 S2 U2 W2 mem2 md2 (p + i) HARU2); unfold SHADOW_OFF; lia).
  rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem ms')) (ms_mem ms') (p + i))
    by (apply (fsw_pf_unp B ly S U W (ms_mem ms') mdc (p + i) HARU); unfold SHADOW_OFF; lia).
  exact (F2 p k i H1 H2 Hi Hnf). }
(* a byte of a block of the entry other than the old buffer is off FP1 *)
assert (OFF : forall p k i, In (p, k) (ablocks B ly S) -> p <> buf - HEAD -> 0 <= i < req_size k -> ~ inFP FP1 (p + i)).
{ intros p k i H1 Hp Hi Hf. destruct (HFP1 _ Hf) as [Hps | (Hc0 & Hb)].
  - apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p k (p + i) HAR H1); [lia | exact (pgt_pstat_img _ Hps)].
  - destruct (OLDB Hc0) as (Hin & Hcp).
    pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
    destruct (fsw_pf_blk_disj B ly S W (unpoison U mem) md p k (buf - HEAD) (cap + HEAD) HAR H1 Hin Hp) as [D|D];
      unfold HEAD in *; lia. }
(* a block of the entry other than the old buffer is disjoint from every block the call created *)
assert (NEWD : forall p k q m, In (p, k) (ablocks B ly S) -> p <> buf - HEAD -> 0 < k ->
  In (q, m) (ablocks B ly2 S2) -> ~ In (q, m) (ablocks B ly S) -> 0 < m ->
  p + req_size k <= q \/ q + req_size m <= p).
{ intros p k q m H1 Hp Hk H2 H3 Hm.
  pose proof (HBK p k H1 Hp) as H1'.
  destruct (Z.eq_dec p q) as [<- | Hne].
  - exfalso. apply H3. rewrite <- (pgt_same_start B ly2 S2 W2 (unpoison U2 mem2) md2 p k m HAR2 H1' H2 Hk Hm).
    exact H1.
  - exact (fsw_pf_blk_disj B ly2 S2 W2 (unpoison U2 mem2) md2 p k q m HAR2 H1' H2 Hne). }
destruct HSK as [[Hbs Ham] | [(p & k & Hpb & Hrb & Hps & Hpk) | [(p & k & Hpb & Hin2 & Hps & Hpk & HU) | (l & Hl & Hll)]]].
- (* nothing is read *)
  subst bs. cbn [length Z.of_nat] in Hlen. subst n.
  split; [unfold zbytes_at; apply garr8_nil|]. split; [apply range_addressable_nil; lia|].
  split; [lia|]. split; [exact Ham|]. split; [intros i Hi; lia|]. intros q m _ _ _ x Hx; lia.
- (* the user bytes of another reader block *)
  rewrite Hlen in Hpk. pose proof Hrb as (Hin2 & Hp16 & Hk0 & _).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) HAR Hin2)
    as (_ & Hp4096 & Hpceil & Hpapp & _).
  assert (RQ : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
  rewrite RQ in Hpceil, Hpapp. unfold in_app, kLowShadowBeg, ASAN_CEIL, HEAD in Hpapp. unfold HEAD in Hpceil, Hp4096.
  assert (Hpn : p - HEAD <> buf - HEAD) by (unfold HEAD; lia).
  pose proof (HBK _ _ Hin2 Hpn) as Hin2'.
  assert (KS : forall i, 0 <= i < n ->
    mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)).
  { intros i Hi. replace (s + i) with (p - HEAD + (s + i - (p - HEAD))) by lia.
    apply (BK (p - HEAD) (k + HEAD)); [exact Hin2 | exact Hin2' | rewrite RQ; unfold HEAD; lia |].
    apply (OFF (p - HEAD) (k + HEAD)); [exact Hin2 | exact Hpn | rewrite RQ; unfold HEAD; lia]. }
  assert (OUT : forall x, s <= x < s + n -> in_ush U2 (shadow_addr x) = false).
  { intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU2))); [lia|].
    exact (fsw_pf_heads_out B ly2 S2 U2 W2 (unpoison U2 mem2) md2 p k x HAR2 FH2 Hin2' Hk0 ltac:(lia)). }
  split.
  { unfold zbytes_at in HZS |- *. apply (garr8_frame tfibsegs _ _ s bs HZS).
    intros a Ha. rewrite Hlen in Ha. replace a with (s + (a - s)) by lia. apply KS. lia. }
  split.
  { apply (fsw_pf_ra_raw (w_H W2) U2 mem2 s n); [lia | lia | exact OUT |].
    apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 (p - HEAD) (k + HEAD) s n
      HAR2 Hin2'); rewrite ?RQ; unfold HEAD; lia. }
  split.
  { intros Hn1. apply (fsw_pf_hull_raw W2 U2 mem2 s n (proj2 (proj2 HARU2))); [lia | lia |].
    apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 (p - HEAD) (k + HEAD) s n
      HAR2 Hin2'); rewrite ?RQ; unfold HEAD; lia. }
  split; [unfold amem_range; lia|]. split; [exact KS|].
  intros q m Hq Hnq Hm0 x Hx Hxq.
  destruct (NEWD (p - HEAD) (k + HEAD) q m Hin2 Hpn ltac:(unfold HEAD; lia) Hq Hnq Hm0) as [D|D];
    rewrite ?RQ in D; unfold HEAD in *; lia.
- (* any other live block, the range avoiding every head of U *)
  rewrite Hlen in Hpk, HU.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p k HAR Hin2) as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & HkM).
  pose proof (req_size_pos k ltac:(lia)) as (RQ1 & RQ2).
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Hpapp.
  pose proof (HBK _ _ Hin2 Hpb) as Hin2'.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  + (* nothing is read: every clause is vacuous but the range's own facts *)
    rewrite Hn0. split.
    { unfold zbytes_at. destruct bs as [|b0 bs']; [apply garr8_nil | cbn [length] in Hlen; lia]. }
    split; [apply range_addressable_nil; lia|]. split; [lia|]. split; [unfold amem_range; lia|].
    split; [intros i Hi; lia|]. intros q m _ _ _ x Hx; lia.
  + assert (Hk0 : 0 < k) by (destruct (Z.eq_dec k 0) as [E0|E0]; [subst k; unfold req_size in Hpk; cbn in Hpk; lia | lia]).
    assert (KS : forall i, 0 <= i < n ->
      mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)).
    { intros i Hi. replace (s + i) with (p + (s + i - p)) by lia.
      apply (BK p k); [exact Hin2 | exact Hin2' | lia |].
      apply (OFF p k); [exact Hin2 | exact Hpb | lia]. }
    assert (OUT : forall x, s <= x < s + n -> in_ush U2 (shadow_addr x) = false).
    { intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU2))); [lia|].
      intros r Hr Hxr. destruct (HU2 r Hr) as [HrU | (m & Hm2 & Hm1 & Hsr & HmR)].
      - destruct (HU r HrU); lia.
      - assert (Hm0 : 0 < m) by (destruct (Z.eq_dec m 0) as [E|E]; [subst m; unfold req_size in HmR; cbn in HmR;
                                                                     unfold HEAD in HmR; lia | ];
                                 destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U2 mem2) md2 _ m HAR2 Hm2)
                                   as (_ & _ & _ & _ & _ & _ & HmM); lia).
        pose proof (req_size_pos m ltac:(lia)) as (Rm1 & Rm2).
        destruct (NEWD p k (fst r) m Hin2 Hpb Hk0 Hm2 Hm1 Hm0) as [D|D]; rewrite Hsr in Hxr; unfold HEAD in *; lia. }
    split.
    { unfold zbytes_at in HZS |- *. apply (garr8_frame tfibsegs _ _ s bs HZS).
      intros a Ha. rewrite Hlen in Ha. replace a with (s + (a - s)) by lia. apply KS. lia. }
    split.
    { apply (fsw_pf_ra_raw (w_H W2) U2 mem2 s n); [lia | lia | exact OUT |].
      apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 p k s n HAR2 Hin2'); lia. }
    split.
    { intros Hn1. apply (fsw_pf_hull_raw W2 U2 mem2 s n (proj2 (proj2 HARU2))); [lia | lia |].
      apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 p k s n HAR2 Hin2'); lia. }
    split; [unfold amem_range; lia|]. split; [exact KS|].
    intros q m Hq Hnq Hm0 x Hx Hxq.
    destruct (NEWD p k q m Hin2 Hpb Hk0 Hq Hnq Hm0) as [D|D]; lia.
- (* a prefix of a read-only literal: fs_img_facts' cstr_ok at the entry and on the memory after the call *)
  destruct (fsw_pf_ro_strs_img s l Hl) as (Hl0 & Hl1).
  assert (Hnl : n <= Z.of_nat (length l) + 1).
  { pose proof (proj1 (Nat2Z.inj_le _ _) Hll) as H'. rewrite Nat2Z.inj_succ in H'. lia. }
  pose proof IMG as (_ & IMG2).
  assert (HARU0 : ARU tfibsegs B ly S U W mem md) by exact (fsw_ARU B STK_put ly S U W regs mem md ch HPREU).
  (* the read-only view at the entry, on the unpoisoned memory *)
  assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem))).
  { intros a Ha Hno Hne. pose proof (fsw_pf_roP_low a Ha) as Ha'.
    rewrite (aview_at tfibsegs (w_H W) (unpoison U mem) mem a); [exact (HRO a Ha Hno Hne)|].
    apply (fsw_pf_unp B ly S U W mem md a HARU0); unfold SHADOW_OFF in *; lia. }
  (* ... at the call, and after it (FSW_rd.arodata_kept: FP1 is closed and holds no read-only byte) *)
  assert (HROc : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms')))
    by exact (arodata_below B W mem (ms_mem ms') SB HRO).
  assert (Hcl : ~ YI16.sink_open_fp FP1).
  { intros (r & Hr & H0). destruct (HFP1 0 (ex_intro _ r (conj Hr H0))) as [Hps | (Hc0 & Hb)].
    - destruct Hps as (r' & Hr' & H0'). unfold FS_PSTAT_FP in Hr'.
      destruct Hr' as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H0'; lia.
    - destruct (OLDB Hc0) as (Hin & _).
      destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin) as (_ & Hb4096 & _).
      unfold HEAD in *. lia. }
  assert (Hro1 : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP1 a).
  { intros a Ha Hf. destruct (HFP1 a Hf) as [Hps | (Hc0 & Hb)].
    - exact (pgt_pstat_not_ro a Ha Hps).
    - destruct (OLDB Hc0) as (Hin & Hcp).
      pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
      apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) a HAR Hin);
        [unfold HEAD in *; lia | exact (FSW_rd.fsw_roP_img a Ha)]. }
  assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2))
    by exact (FSW_rd.arodata_kept B STK_fuzz_realloc (spZ (ms_regs ms')) FP1 ly S U W (ms_mem ms') mdc ly2 S2 U2 W2
                mem2 md2 kc HJc HARU (proj1 (proj2 HARU2)) (proj2 (proj2 HARU2)) Hcl Hro1 HROc).
  assert (HRO2' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) (unpoison U2 mem2))).
  { intros a Ha Hno Hne. pose proof (fsw_pf_roP_low a Ha) as Ha'.
    rewrite (aview_at tfibsegs (w_H W2) (unpoison U2 mem2) mem2 a); [exact (HRO2 a Ha Hno Hne)|].
    apply (fsw_pf_unp B ly2 S2 U2 W2 mem2 md2 a HARU2); unfold SHADOW_OFF in *; lia. }
  destruct (IMG2 ly S W (unpoison U mem) md HAR HRO') as (_ & _ & HSTRS & _).
  destruct (proj1 (Forall_forall _ _) HSTRS (s, l) Hl) as (Hcs & _). cbn [fst snd] in Hcs.
  destruct Hcs as ((Hga & _) & _ & _ & _ & Hamr & _ & _ & _).
  destruct (IMG2 ly2 S2 W2 (unpoison U2 mem2) md2 HAR2 HRO2') as (_ & _ & HSTRS2 & _).
  destruct (proj1 (Forall_forall _ _) HSTRS2 (s, l) Hl) as (Hcs2 & _). cbn [fst snd] in Hcs2.
  destruct Hcs2 as ((Hga2 & _) & _ & _ & _ & _ & HRA2 & HHULL2 & _).
  (* the image bytes are no user-poisoned shadow byte, at either end *)
  assert (RAWE : forall x, 0x10000 <= x < 0x5fd000 ->
    mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) x = mbyte tfibsegs (mrestrict (w_H W) mem) x).
  { intros x Hx. unfold mbyte, mrestrict.
    rewrite (fsw_pf_unp B ly S U W mem md x HARU0) by (unfold SHADOW_OFF; lia). reflexivity. }
  assert (RAW2 : forall x, 0x10000 <= x < 0x5fd000 ->
    mbyte tfibsegs (mrestrict (w_H W2) (unpoison U2 mem2)) x = mbyte tfibsegs (mrestrict (w_H W2) mem2) x).
  { intros x Hx. unfold mbyte, mrestrict.
    rewrite (fsw_pf_unp B ly2 S2 U2 W2 mem2 md2 x HARU2) by (unfold SHADOW_OFF; lia). reflexivity. }
  assert (KS : forall i, 0 <= i < n ->
    mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)).
  { intros i Hi.
    assert (Hil : (Z.to_nat i < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    destruct (Hga (Z.to_nat i) Hil) as (V1 & _). destruct (Hga2 (Z.to_nat i) Hil) as (V2 & _).
    specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)).
    replace (s + Z.of_nat (Z.to_nat i) + Z.of_nat 0) with (s + i) in V1, V2 by lia.
    rewrite <- (RAWE (s + i)) by lia. rewrite <- (RAW2 (s + i)) by lia. rewrite V1, V2. reflexivity. }
  assert (OUT : forall x, s <= x < s + n -> in_ush U2 (shadow_addr x) = false).
  { intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU2))); [lia|].
    apply (fsw_pf_img_out B ly2 S2 U2 W2 (unpoison U2 mem2) md2 x HAR2 (proj1 (proj2 HARU2))).
    apply fsw_pf_in_img. lia. }
  split.
  { unfold zbytes_at in HZS |- *. apply (garr8_frame tfibsegs _ _ s bs HZS).
    intros a Ha. rewrite Hlen in Ha. replace a with (s + (a - s)) by lia. apply KS. lia. }
  split.
  { apply (fsw_pf_ra_raw (w_H W2) U2 mem2 s n); [lia | lia | exact OUT |].
    eapply range_addressable_sub; [exact HRA2 | lia | lia]. }
  split.
  { intros Hn1. apply (fsw_pf_hull_raw W2 U2 mem2 s n (proj2 (proj2 HARU2))); [lia | lia |].
    intros t Ht. apply HHULL2. unfold shadow_addr in *. lia. }
  split; [unfold amem_range in *; lia|]. split; [exact KS|].
  intros q m Hq _ _ x Hx Hxq.
  apply (blk_img tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 q m x HAR2 Hq); [lia|].
  apply fsw_pf_in_img. lia.
Qed.

(* blocks_bytes is the sum of the block sizes (as A/AD1r.v:608 blocks_bytes_ablocks, over Reusable's bsum) *)
Lemma pgt_bb : forall ly0 S0, blocks_bytes S0 = YCbq.bsum (ablocks B ly0 S0).
Proof.
intros ly0 S0.
assert (E : blocks_bytes S0 = fold_right (fun b acc => snd b + acc) 0 (blocks S0)).
{ unfold blocks_bytes, blocks. induction (st_chunks S0) as [|k ks IH]; cbn; [reflexivity|].
  destruct (is_alloc k); cbn; rewrite IH; reflexivity. }
rewrite E. clear E. unfold ablocks, YCbq.bsum.
induction (blocks S0) as [|b l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.

(* ---- THE TOP LEMMA: from the call of fuzz_realloc to put_spec's post. fuzz_realloc_spec's three outcomes: refused
   (cnt = fail; pgt_refused), granted from a NULL buffer (cap = 0, its p = 0 arm, journal 1; pgt_granted) and granted
   from a live buffer (cap <> 0, its p <> 0 arm, journal 3; pgt_granted). put_spec's count wevk cap st' is 1 at
   cap = 0 and 3 at cap <> 0 (pgt_put1), at or above each arm's journal (ajournal's k only rises). ---- *)
Lemma pgt_run :
  SRr tfibsegs W (mkCfg ms' mdc)
    (put_post B ly S U W regs mem md ot o s n buf cap 0 text bs live peak cnt fail).
Proof.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & _).
pose proof HSRC as (Hs0 & Hsn).
pose proof HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
pose proof HGLOB as (G1 & G2 & G3 & G4 & Hlp & Hpk & Hcnt0 & Hfl).
assert (HARU0 : ARU tfibsegs B ly S U W mem md) by exact (fsw_ARU B STK_put ly S U W regs mem md ch HPREU).
destruct pgt_callee_pre as (ch1 & HPREc).
destruct pgt_call_regs as (Ems & R1 & R2 & _ & _ & _ & _ & R10 & R11 & _).
assert (SB : same_below mem (ms_mem ms') alloc_ceiling) by (intros x Hx; apply HMF; lia).
assert (Hcls : cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j)
  by (destruct Hcase as [(E & _) | (Hj & _)]; [left; exact E | right; exact Hj]).
assert (Hcj : exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j)
  by (rewrite Hcnew; exact (proj1 (put_grow_newcap_class cap _ Hcls HCAP HWM))).
unfold WMAX in HWM, HCAP, HcW.
assert (Hn0 : 0 <= n) by lia.
assert (Hlen0 : 0 <= Z.of_nat (length text)) by lia.
assert (Bc : bsz c = c + HEAD) by (unfold bsz; rewrite (proj2 (Z.eqb_neq c 0)) by lia; reflexivity).
assert (RQc : req_size (c + HEAD) = c + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (c + 16) 0); lia).
(* ---- the model: put1's two outcomes, its journal count and its budget ---- *)
pose proof pgt_put1 as HPUT.
assert (HWV : wevk cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = if cap =? 0 then 1 else 3).
{ rewrite HPUT. unfold wevk, wev0, wcalls. destruct (cnt =? fail); cbn [WriterApp.w_calls length Z.of_nat];
  destruct (cap =? 0); reflexivity. }
assert (HWC : wcalls (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = 1)
  by (rewrite HPUT; unfold wcalls; destruct (cnt =? fail); reflexivity).
pose proof HBUD as (Bev & Bbb & Blv & Bcn). rewrite HWV in Bev. rewrite HWC in Bcn.
assert (Bev0 : cap = 0 -> st_nev S + 1 <= EV_MAX)
  by (intros E; rewrite (proj2 (Z.eqb_eq _ _) E) in Bev; exact Bev).
assert (Bev3 : cap <> 0 -> st_nev S + 3 <= EV_MAX)
  by (intros E; rewrite (proj2 (Z.eqb_neq _ _) E) in Bev; exact Bev).
assert (HCG : cnt <> fail -> WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = c).
{ intros Hne. rewrite HPUT, (proj2 (Z.eqb_neq _ _) Hne). reflexivity. }
(* ---- the buffer: none (cap = 0), or a live reader block whose head is in U ---- *)
assert (HCZ : cap = 0 -> buf = 0 /\ text = []).
{ intros E. destruct Hcase as [(_ & Hb & Ht) | ((j & Hj & Hcj') & _)]; [split; assumption|].
  exfalso. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia. }
assert (HCN : cap <> 0 -> (exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ fs_rblock tfibsegs B ly S W mem buf cap /\
  Z.of_nat (length text) < cap /\ zbytes_at tfibsegs W mem buf (text ++ [0])).
{ intros E. destruct Hcase as [(Hc & _) | Hx]; [contradiction | exact Hx]. }
assert (HCB : cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S) /\ 4096 + HEAD <= buf /\ 0 < cap /\
  buf + cap <= alloc_ceiling /\ in_app (buf - HEAD) (cap + HEAD)).
{ intros E. destruct (HCN E) as (_ & (Hin & _ & Hcp & _) & _).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin)
    as (_ & Hb4096 & Hbc & Happ & _).
  assert (RQ : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
  rewrite RQ in Hbc, Happ.
  split; [exact Hin|]. split; [unfold HEAD in *; lia|]. split; [exact Hcp|]. split; [unfold HEAD in *; lia | exact Happ]. }
(* the old buffer's cap bytes, every one present (a live block's bytes are), as a list *)
set (old := pgt_bytes (mrestrict (w_H W) (ms_mem ms')) buf (Z.to_nat cap)).
assert (HOLD : cap <> 0 -> length old = Z.to_nat cap /\ zbytes_at tfibsegs W (ms_mem ms') buf old).
{ intros E. destruct (HCB E) as (Hin & Hb & Hcp & Hbc & Hbs).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin) as (_ & _ & _ & _ & Hbp & _).
  assert (RQ : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
  unfold zbytes_at. apply pgt_bytes_ok. intros j Hj.
  assert (Hj' : Z.of_nat j < cap) by (apply Nat2Z.inj_lt in Hj; rewrite Z2Nat.id in Hj by lia; exact Hj).
  apply pgt_mbyte_present. apply HPRK.
  destruct (Hbp (buf + Z.of_nat j) ltac:(rewrite RQ; unfold HEAD; lia)) as ((Hh & b & Hbb) & _).
  split; [exact Hh|]. exists b.
  rewrite <- (fsw_pf_unp B ly S U W mem md (buf + Z.of_nat j) HARU0);
    [exact Hbb | unfold in_app, HEAD, SHADOW_OFF, kLowShadowBeg in *; lia
    | unfold in_app, HEAD, SHADOW_OFF, kLowShadowBeg in *; lia]. }
(* ---- fuzz_realloc's premises ---- *)
assert (HPK : (buf = 0 /\ cap = 0 /\ old = []) \/
   (buf <> 0 /\ (exists U1 U2, U = U1 ++ (buf - HEAD, HEAD) :: U2) /\
    fs_rblock tfibsegs B ly S W (ms_mem ms') buf cap /\ Z.of_nat (length old) = cap /\
    zbytes_at tfibsegs W (ms_mem ms') buf old /\ cap <= live)).
{ destruct (Z.eq_dec cap 0) as [E|E].
  - left. destruct (HCZ E) as (Hb & _). split; [exact Hb|]. split; [exact E|]. unfold old. rewrite E. reflexivity.
  - right. destruct (HCB E) as (Hin & Hb & Hcp & Hbc & Hbs). destruct (HOLD E) as (Hl & Hz).
    destruct (HCN E) as (_ & (_ & Hb16 & _ & Vh) & _).
    split; [unfold HEAD in Hb; lia|]. split; [exact (in_split _ _ (HHEAD E))|].
    split.
    { split; [exact Hin|]. split; [exact Hb16|]. split; [exact Hcp|].
      intros k Hk. rewrite (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling _ SB) by (unfold HEAD in *; lia).
      exact (Vh k Hk). }
    split; [rewrite Hl; lia|]. split; [exact Hz | exact HCL]. }
assert (HGc : fs_glob tfibsegs W (ms_mem ms') live peak cnt fail).
{ assert (VB : forall g v, 0x10000 <= g -> g + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
    val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) g 8 v).
  { intros g v Hg1 Hg2 Hv k Hk. rewrite (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling _ SB) by lia.
    exact (Hv k Hk). }
  unfold fs_glob, fs_glob_at.
  split; [apply VB; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1]|].
  split; [apply VB; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2]|].
  split; [apply VB; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3]|].
  split; [apply VB; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4]|].
  repeat split; lia. }
assert (HEV : (buf = 0 -> st_nev S + EV_fuzz_malloc <= EV_MAX) /\ (buf <> 0 -> st_nev S + 3 <= EV_MAX)).
{ split; intros Hb.
  - destruct (Z.eq_dec cap 0) as [E|E]; [pose proof (Bev0 E); unfold EV_fuzz_malloc; lia|].
    destruct (HCB E) as (_ & Hb' & _). unfold HEAD in Hb'. lia.
  - destruct (Z.eq_dec cap 0) as [E|E]; [destruct (HCZ E); contradiction | exact (Bev3 E)]. }
assert (HBR : cnt <> fail -> blocks_bytes S + (c + HEAD) <= LIVE_MAX).
{ intros Hne. rewrite (HCG Hne) in Bbb.
  assert (Bz : bsz cap <= c + HEAD) by (unfold bsz; destruct (Z.eqb_spec cap 0); unfold HEAD; lia).
  lia. }
assert (HLR : cnt <> fail -> live + c < 2 ^ 64) by (intros Hne; rewrite (HCG Hne) in Blv; lia).
(* the old footprint is FS_PSTAT_FP (image) plus, at cap <> 0, the old block (inFP through wbuf_fp) *)
assert (HFP0 : fsw_fp_sub B ly S ly S [] (FS_PSTAT_FP ++ wbuf_fp buf cap) FS_PSTAT_FP).
{ intros a Ha. right. right. left. split; [|exact (pgt_pstat_img a Ha)].
  destruct Ha as (r & Hr & Hra). exists r. split; [apply in_or_app; left; exact Hr | exact Hra]. }
(* ---- the call ---- *)
rewrite Ems.
eapply SRr_bind.
{ exact (HREALLOC ly S U W (ms_regs ms') (ms_mem ms') mdc ch1 buf cap c old live peak cnt fail HPREc FH R10 R11
    ltac:(lia) ltac:(unfold MALLOC_MAX, HEAD; lia) HGc HLR ltac:(lia) HPK HEV HBR). }
intros W2 c2 _ HPOST.
destruct HPOST as [(Hcf & HP) | [(Hcf & Hb0 & res & HP) | (Hcf & Hbn & U1 & U2 & res & HU & HP)]].
- (* ======== refused (cnt = fail) ======== *)
  destruct HP as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HPR2 & R10r & HAB & FH2 & HGL2).
  destruct (pgt_resume FS_PSTAT_FP 0 ly2 S2 U W2 regs2 mem2 md2 0 0 HJc HFP0 OK2 PO2 HPR2)
    as (HJ2 & HARU2 & KEEPE & HS1).
  destruct (pgt_src_after FS_PSTAT_FP 0 ly2 S2 U W2 mem2 md2 HJc HARU2 FH2
    ltac:(intros a Ha; left; exact Ha) ltac:(intros p k Hp _; rewrite HAB; exact Hp) ltac:(intros r Hr; left; exact Hr))
    as (_ & _ & _ & _ & SKEEP & _).
  (* o's buffer as it stands after the call: the old block is live at both ends and off FS_PSTAT_FP *)
  assert (HCASE2 : (cap = 0 /\ buf = 0 /\ text = []) \/
    ((exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ fs_rblock tfibsegs B ly2 S2 W2 mem2 buf cap /\
     Z.of_nat (length text) < cap /\ zbytes_at tfibsegs W2 mem2 buf (text ++ [0]))).
  { destruct (Z.eq_dec cap 0) as [E|E]; [left; destruct (HCZ E) as (Hb & Ht); split; [exact E | split; assumption]|right].
    destruct (HCN E) as (Hj & (Hin & Hb16 & Hcp & Vh) & Hlt & Hzt).
    destruct (HCB E) as (_ & Hb & _ & Hbc & Hbs).
    pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    assert (RQ : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
    assert (Hin2 : In (buf - HEAD, cap + HEAD) (ablocks B ly2 S2)) by (rewrite HAB; exact Hin).
    assert (KB : forall i, 0 <= i < cap + HEAD ->
      mbyte tfibsegs (mrestrict (w_H W2) mem2) (buf - HEAD + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (buf - HEAD + i)).
    { intros i Hi.
      rewrite <- (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling (buf - HEAD + i) SB) by (unfold HEAD in *; lia).
      apply (mbyte_of_aview tfibsegs).
      rewrite <- (aview_at tfibsegs (w_H W2) (unpoison U mem2) mem2 (buf - HEAD + i))
        by (apply (fsw_pf_unp B ly2 S2 U W2 mem2 md2 (buf - HEAD + i) HARU2);
            unfold in_app, HEAD, SHADOW_OFF, kLowShadowBeg in *; lia).
      rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem ms')) (ms_mem ms') (buf - HEAD + i))
        by (apply (fsw_pf_unp B ly S U W (ms_mem ms') mdc (buf - HEAD + i) HARU);
            unfold in_app, HEAD, SHADOW_OFF, kLowShadowBeg in *; lia).
      apply (F2 (buf - HEAD) (cap + HEAD) i Hin Hin2 ltac:(rewrite RQ; lia)).
      intros Hf. apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) (buf - HEAD + i)
        HAR Hin); [rewrite RQ; lia | exact (pgt_pstat_img _ Hf)]. }
    split; [exact Hj|]. split; [|split; [exact Hlt|]].
    - split; [exact Hin2|]. split; [exact Hb16|]. split; [exact Hcp|].
      intros k Hk. rewrite (KB (Z.of_nat k)) by (unfold HEAD; lia). exact (Vh k Hk).
    - unfold zbytes_at in Hzt |- *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) Hzt).
      intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
      replace a with (buf - HEAD + (a - (buf - HEAD))) by lia. apply KB. unfold HEAD. lia. }
  rewrite R1.
  eapply SRr_mono.
  { exact (pgt_refused 0 ly2 S2 W2 regs2 mem2 md2 0 (wevk cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
      HJ2 HARU2 HS1 HPR2 R10r KEEPE HCASE2 SKEEP HGL2 ltac:(rewrite HWV; destruct (cap =? 0); cbv beta iota; lia)). }
  intros W' c' _ HQ.
  destruct HQ as (ly' & S' & regs' & mem' & md' & Hc' & HJ' & OK' & PO' & HP' & (-> & -> & HWO & HWK & HGL' & HSK')).
  unfold put_post. exists (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs), buf, U.
  split; [reflexivity|]. split; [left; split; reflexivity|].
  unfold wpost, fpostU. exists ly2, S2, regs', mem', md'.
  split; [exact Hc'|]. split; [exact HJ'|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP'|].
  rewrite HPUT, (proj2 (Z.eqb_eq _ _) Hcf).
  cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
  split; [exact HWO|].
  split.
  { apply put_grow_kept_refused; [unfold WMAX; lia | lia | lia |].
    rewrite (pgt_bb ly2 S2), (pgt_bb ly S), HAB. lia. }
  split; [left; split; [reflexivity | split; [reflexivity | rewrite HAB; reflexivity]]|].
  split; [exact HWK|].
  split; [|exact HSK'].
  exists peak. split; [lia|]. rewrite Z.mod_small by lia. replace (live + cap - cap) with live by lia. exact HGL'.
- (* ======== granted from a NULL buffer (cap = 0) ======== *)
  assert (Hc0 : cap = 0)
    by (destruct (Z.eq_dec cap 0) as [E|E]; [exact E | destruct (HCB E) as (_ & Hb & _); unfold HEAD in Hb; lia]).
  destruct (HCZ Hc0) as (_ & Ht0).
  destruct HP as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HPR2 & R10g & Hres & HAB & FH2 & HRB2 & HGL2).
  set (Unew := U ++ [(res - HEAD, HEAD)]) in *.
  destruct (pgt_resume FS_PSTAT_FP 1 ly2 S2 Unew W2 regs2 mem2 md2 res (res + Z.of_nat (length text) + n)
    HJc HFP0 OK2 PO2 HPR2) as (HJ2 & HARU2 & KEEPE & HS1).
  assert (Hin2 : In (res - HEAD, c + HEAD) (ablocks B ly2 S2))
    by (rewrite HAB; apply in_or_app; right; left; reflexivity).
  assert (HNEW : ~ In (res - HEAD, c + HEAD) (ablocks B ly S)).
  { intros Hx. pose proof (al_blocks _ _ LAWS ly2 S2 W2 _ md2 _ _ (proj1 HARU2) Hin2) as (_ & _ & _ & _ & _ & PW & _).
    rewrite HAB in PW. apply (pgt_new_once (ablocks B ly S) [] (res - HEAD, c + HEAD) ltac:(cbn [snd]; unfold HEAD; lia) PW).
    rewrite app_nil_r. exact Hx. }
  destruct (pgt_src_after FS_PSTAT_FP 1 ly2 S2 Unew W2 mem2 md2 HJc HARU2 FH2
    ltac:(intros a Ha; left; exact Ha)
    ltac:(intros p k Hp _; rewrite HAB; apply in_or_app; left; exact Hp)
    ltac:(intros r Hr; unfold Unew in Hr; apply in_app_or in Hr as [Hr | [<- | []]]; [left; exact Hr | right];
          exists (c + HEAD); cbn [fst snd]; split; [exact Hin2|]; split; [exact HNEW|]; split; [reflexivity|];
          rewrite RQc; unfold HEAD; lia))
    as (HZS2 & SRA2 & SHULL2 & SAMR & SKEEP & SNEW).
  assert (SDISJ : forall x, s <= x < s + n -> ~ (res - HEAD <= x < res + c)).
  { intros x Hx Hxr. apply (SNEW (res - HEAD) (c + HEAD) Hin2 HNEW ltac:(unfold HEAD; lia) x Hx).
    rewrite RQc. unfold HEAD in *. lia. }
  assert (HTXT : zbytes_at tfibsegs W2 mem2 res text) by (rewrite Ht0; unfold zbytes_at; apply garr8_nil).
  assert (HGLOB2 : fs_glob tfibsegs W2 mem2 (live - cap + c) (Z.max peak (live - cap + c)) (cnt + 1) fail)
    by (rewrite Hc0; replace (live - 0 + c) with (live + c) by lia; exact HGL2).
  rewrite R1.
  eapply SRr_mono.
  { exact (pgt_granted 1 ly2 S2 Unew W2 regs2 mem2 md2 res
      (wevk cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
      HJ2 HARU2 HS1 HPR2 R10g Hres (HRB2 ltac:(lia)) HNEW FH2 HTXT KEEPE HZS2 SRA2 SHULL2 SAMR SDISJ SKEEP HGLOB2 Hcj
      ltac:(rewrite HWV, (proj2 (Z.eqb_eq cap 0) Hc0); cbv beta iota; lia)). }
  intros W' c' _ HQ.
  destruct HQ as (ly' & S' & regs' & mem' & md' & Hc' & HJ' & OK' & PO' & HP' & (-> & -> & HWO & HWK & HGL' & HSK')).
  unfold put_post. exists (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs), res, Unew.
  split; [reflexivity|]. split; [right; right; split; [exact Hc0 | reflexivity]|].
  unfold wpost, fpostU. exists ly2, S2, regs', mem', md'.
  split; [exact Hc'|]. split; [exact HJ'|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP'|].
  rewrite HPUT, (proj2 (Z.eqb_neq _ _) Hcf).
  cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
  split; [exact HWO|].
  split.
  { unfold wbudget_kept. split; [unfold WMAX; lia|]. split; [|rewrite Z.mod_small by lia; lia].
    rewrite (pgt_bb ly2 S2), (pgt_bb ly S), HAB, YCbq.bsum_app, Bc, Hc0, put_grow_bsz_0.
    change (YCbq.bsum [(res - HEAD, c + HEAD)]) with (c + HEAD + 0). lia. }
  split.
  { right. left. split; [exact Hc0|]. exists (ablocks B ly S), []. split; [rewrite HAB; reflexivity | apply app_nil_r]. }
  split; [exact HWK|].
  split; [|exact HSK'].
  exists (Z.max peak (live - cap + c)). split; [lia|].
  replace (live + c - cap) with (live - cap + c) by lia. rewrite Z.mod_small by lia. exact HGL'.
- (* ======== granted from a live buffer (cap <> 0) ======== *)
  assert (Hcn : cap <> 0) by (intros E; destruct (HCZ E); contradiction).
  destruct (HCB Hcn) as (Hin & Hb & Hcp & Hbc & Hbs).
  destruct (HCN Hcn) as (_ & HRB & Hlt & Hzt).
  destruct HP as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HPR2 & R10g & Hres &
    (b1 & b2 & c1 & c2' & HA & HA' & Hcc) & FH2 & HRB2 & HZR & HGL2).
  set (Unew := U1 ++ U2 ++ [(res - HEAD, HEAD)]) in *.
  assert (RQ : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
  assert (Bcap : bsz cap = cap + HEAD) by (unfold bsz; rewrite (proj2 (Z.eqb_neq cap 0) Hcn); reflexivity).
  assert (HFP : fsw_fp_sub B ly S ly S [] (FS_PSTAT_FP ++ wbuf_fp buf cap)
                  (FS_PSTAT_FP ++ ablocks_fp [(buf - HEAD, cap + HEAD)])).
  { intros a (r & Hr & Hra). apply in_app_or in Hr as [Hr | Hr].
    - right. right. left. split; [exists r; split; [apply in_or_app; left; exact Hr | exact Hra]|].
      exact (pgt_pstat_img a (ex_intro _ r (conj Hr Hra))).
    - unfold ablocks_fp in Hr. cbn [map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra.
      left. split; [|exists (buf - HEAD), (cap + HEAD); split; [exact Hin | exact Hra]].
      exists (buf - HEAD, buf + cap). split.
      + apply in_or_app. right. unfold wbuf_fp. rewrite (proj2 (Z.eqb_neq cap 0) Hcn). left. reflexivity.
      + cbn [fst snd]. rewrite RQ in Hra. unfold HEAD in *. lia. }
  destruct (pgt_resume _ 3 ly2 S2 Unew W2 regs2 mem2 md2 res (res + Z.of_nat (length text) + n) HJc HFP OK2 PO2 HPR2)
    as (HJ2 & HARU2 & KEEPE & HS1).
  assert (Hin2 : In (res - HEAD, c + HEAD) (ablocks B ly2 S2))
    by (rewrite HA'; apply in_or_app; right; left; reflexivity).
  assert (HNEW : ~ In (res - HEAD, c + HEAD) (ablocks B ly S)).
  { pose proof (al_blocks _ _ LAWS ly2 S2 W2 _ md2 _ _ (proj1 HARU2) Hin2) as (_ & _ & _ & _ & _ & PW & _).
    rewrite HA' in PW. pose proof (pgt_new_once c1 c2' (res - HEAD, c + HEAD) ltac:(cbn [snd]; unfold HEAD; lia) PW) as NO.
    rewrite Hcc in NO. intros Hx. rewrite HA in Hx. apply in_app_or in Hx as [Hx | [Hx | Hx]].
    - apply NO. apply in_or_app. left. exact Hx.
    - injection Hx as _ Hx. lia.
    - apply NO. apply in_or_app. right. exact Hx. }
  destruct (pgt_src_after _ 3 ly2 S2 Unew W2 mem2 md2 HJc HARU2 FH2
    ltac:(intros a (r & Hr & Hra); apply in_app_or in Hr as [Hr | Hr]; [left; exists r; split; assumption|];
          right; split; [exact Hcn|]; unfold ablocks_fp in Hr; cbn [map In] in Hr; destruct Hr as [<- | []];
          cbn [fst snd] in Hra; rewrite RQ in Hra; unfold HEAD in *; lia)
    ltac:(intros p k Hp Hpn; rewrite HA in Hp; rewrite HA';
          assert (Hp' : In (p, k) (b1 ++ b2))
            by (apply in_app_or in Hp as [Hp | [Hp | Hp]];
                [apply in_or_app; left; exact Hp | injection Hp as Hp _; exfalso; lia | apply in_or_app; right; exact Hp]);
          rewrite <- Hcc in Hp'; apply in_app_or in Hp' as [Hp' | Hp']; apply in_or_app;
          [left; exact Hp' | right; right; exact Hp'])
    ltac:(intros r Hr; unfold Unew in Hr; apply in_app_or in Hr as [Hr | Hr];
          [left; rewrite HU; apply in_or_app; left; exact Hr|];
          apply in_app_or in Hr as [Hr | [<- | []]]; [left; rewrite HU; apply in_or_app; right; right; exact Hr | right];
          exists (c + HEAD); cbn [fst snd]; split; [exact Hin2|]; split; [exact HNEW|]; split; [reflexivity|];
          rewrite RQc; unfold HEAD; lia))
    as (HZS2 & SRA2 & SHULL2 & SAMR & SKEEP & SNEW).
  assert (SDISJ : forall x, s <= x < s + n -> ~ (res - HEAD <= x < res + c)).
  { intros x Hx Hxr. apply (SNEW (res - HEAD) (c + HEAD) Hin2 HNEW ltac:(unfold HEAD; lia) x Hx).
    rewrite RQc. unfold HEAD in *. lia. }
  (* the text in the new buffer: fuzz_realloc kept the old buffer's cap bytes, whose first len are the text *)
  assert (HTXT : zbytes_at tfibsegs W2 mem2 res text).
  { destruct (HOLD Hcn) as (Hlo & Hzo).
    rewrite Z.min_l in HZR by lia. rewrite <- Hlo, firstn_all in HZR.
    assert (Hzt' : zbytes_at tfibsegs W (ms_mem ms') buf (text ++ [0])).
    { unfold zbytes_at in Hzt |- *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) Hzt).
      intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
      apply (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling a SB). unfold HEAD in *. lia. }
    unfold zbytes_at in HZR, Hzo, Hzt' |- *. intros j Hj.
    assert (Hjo : (j < length old)%nat) by (rewrite Hlo; apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia).
    assert (Hjt : (j < length (text ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (pgt_garr8_nth _ buf (text ++ [0]) old j Hzt' Hzo Hjt Hjo) as Ej.
    rewrite app_nth1 in Ej by exact Hj. rewrite Ej. exact (HZR j Hjo). }
  rewrite R1.
  eapply SRr_mono.
  { exact (pgt_granted 3 ly2 S2 Unew W2 regs2 mem2 md2 res
      (wevk cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
      HJ2 HARU2 HS1 HPR2 R10g Hres (HRB2 ltac:(lia)) HNEW FH2 HTXT KEEPE HZS2 SRA2 SHULL2 SAMR SDISJ SKEEP HGL2 Hcj
      ltac:(rewrite HWV, (proj2 (Z.eqb_neq cap 0) Hcn); cbv beta iota; lia)). }
  intros W' c' _ HQ.
  destruct HQ as (ly' & S' & regs' & mem' & md' & Hc' & HJ' & OK' & PO' & HP' & (-> & -> & HWO & HWK & HGL' & HSK')).
  unfold put_post. exists (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs), res, Unew.
  split; [reflexivity|]. split; [right; left; exists U1, U2; split; [exact HU | reflexivity]|].
  unfold wpost, fpostU. exists ly2, S2, regs', mem', md'.
  split; [exact Hc'|]. split; [exact HJ'|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP'|].
  rewrite HPUT, (proj2 (Z.eqb_neq _ _) Hcf).
  cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
  split; [exact HWO|].
  split.
  { unfold wbudget_kept. split; [unfold WMAX; lia|]. split; [|rewrite Z.mod_small by lia; lia].
    assert (Eb : YCbq.bsum c1 + YCbq.bsum c2' = YCbq.bsum b1 + YCbq.bsum b2)
      by (rewrite <- !YCbq.bsum_app, Hcc; reflexivity).
    rewrite (pgt_bb ly2 S2), (pgt_bb ly S), HA, HA', !YCbq.bsum_app, !YCbq.bsum_cons. cbn [snd].
    rewrite Bc, Bcap. lia. }
  split.
  { right. right. exists b1, b2, c1, c2'. split; [exact HA|]. split; [exact HA' | exact Hcc]. }
  split; [exact HWK|].
  split; [|exact HSK'].
  exists (Z.max peak (live - cap + c)). split; [lia|].
  replace (live + c - cap) with (live - cap + c) by lia. rewrite Z.mod_small by lia. exact HGL'.
Qed.

End pgt.
