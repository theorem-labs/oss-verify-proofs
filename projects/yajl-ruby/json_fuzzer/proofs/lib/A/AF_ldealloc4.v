(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA MmStep AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow NodesA_mm BackingAlgebraA NodesA_madv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed X_mmap_fixed_srz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanRepFrame AsanFrame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_base AF_place AF_lkit AF_kit AF_kit2 AF_unwind AF_gbb AF_poison AF_premap1 AF_premap2 AM_memset AF_mmfix0
  AF_ldealloc1 AF_ldealloc2 AF_ldealloc3 A_policy5 A_bundle A_benv5 A_mmchk5 A_balloc5 A_bpolicy5 A_bevents5 A_bevents5c.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanLayout.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import CompatE2 LiaA NodesA_mmW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma last_of_nth : forall {X} (l : list X) i c d, nth_error l i = Some c -> Datatypes.S i = length l -> List.last l d = c.
Proof. aceil.
  intros X l. induction l as [|x l IH]; intros i c d Hn Hl; [destruct i; discriminate|].
  destruct l as [|y l'].
  - destruct i; [cbn in Hn; injection Hn as ->; reflexivity| cbn in Hl; lia].
  - destruct i as [|i]; [cbn in Hl; lia|]. cbn in Hn. change (List.last (x :: y :: l') d) with (List.last (y :: l') d).
    eapply IH; [exact Hn| cbn in Hl |- *; lia].
Qed.

Lemma last_nth : forall {X} (l : list X) d, l <> [] -> nth_error l (length l - 1) = Some (List.last l d).
Proof. aceil.
  intros X l. induction l as [|x l IH]; intros d Hne; [congruence|].
  destruct l as [|y l']; [reflexivity|].
  change (List.last (x :: y :: l') d) with (List.last (y :: l') d).
  replace (length (x :: y :: l') - 1)%nat with (Datatypes.S (length (y :: l') - 1)) by (cbn; lia).
  cbn [nth_error]. apply IH. discriminate.
Qed.

Lemma nth_error_removelast : forall {X} (l : list X) j x,
  nth_error (removelast l) j = Some x -> nth_error l j = Some x /\ (Datatypes.S j < length l)%nat.
Proof. aceil.
  intros X l. induction l as [|y l IH]; intros j x H; [cbn in H; destruct j; discriminate|].
  destruct l as [|z l']; [cbn in H; destruct j; discriminate|].
  change (removelast (y :: z :: l')) with (y :: removelast (z :: l')) in H.
  destruct j as [|j]; cbn in H.
  - injection H as ->. split; [reflexivity| cbn; lia].
  - destruct (IH j x H) as [H1 H2]. split; [exact H1| cbn in H2 |- *; lia].
Qed.

Lemma length_list_setn : forall {X} (l : list X) k x, length (list_setn l k x) = length l.
Proof. aceil. intros X l. induction l as [|y l IH]; intros [|k] x; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma nth_error_list_setn : forall {X} (l : list X) k x j y,
  nth_error (list_setn l k x) j = Some y -> (j = k /\ y = x) \/ (j <> k /\ nth_error l j = Some y).
Proof. aceil.
  intros X l. induction l as [|z l IH]; intros k x j y H; [cbn in H; destruct j; discriminate|].
  destruct k as [|k]; destruct j as [|j]; cbn in H.
  - injection H as ->. left. split; reflexivity.
  - right. split; [lia| exact H].
  - right. split; [lia| exact H].
  - destruct (IH k x j y H) as [[-> ->]|[NE Hn]]; [left; split; reflexivity| right; split; [lia| exact Hn]].
Qed.

Lemma errno_is_err : forall r, Prelude.errno_ret_in Mmap.mmap_errnos r = true -> is_err r = true.
Proof. aceil.
  intros r H. unfold Prelude.errno_ret_in, Mmap.mmap_errnos in H. cbn [existsb] in H. rewrite Bool.orb_false_r in H.
  apply bv_eqb_eq in H. subst r. vm_compute. reflexivity.
Qed.

Lemma is_err_small : forall z, 0 <= z < 2^47 -> is_err (Z_to_bv 64 z) = false.
Proof. aceil. intros z Hz. unfold is_err. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64); lia). apply Z.ltb_ge. lia. Qed.

Lemma rw_cells_CB_merge3 : forall m X n1 n2 n3 (l1 l2 l3 : list byte),
  rw_cells asegs m X [CB n1 l1] -> rw_cells asegs m (X + Z.of_nat n1) [CB n2 l2] -> rw_cells asegs m (X + Z.of_nat n1 + Z.of_nat n2) [CB n3 l3] ->
  rw_cells asegs m X [CB (n1 + n2 + n3)%nat (l1 ++ l2 ++ l3)].
Proof. aceil.
  intros m X n1 n2 n3 l1 l2 l3 [[W1 B1] (Wa & Wb & Wr)] [[W2 B2] (Va & Vb & Vr)] [[W3 B3] (Ua & Ub & Ur)].
  cbn in W1, W2, W3. destruct W1 as [L1 _], W2 as [L2 _], W3 as [L3 _].
  cbn [cells_bytes cbytes] in B1, B2, B3. rewrite app_nil_r in B1, B2, B3.
  cbn [cells_size csize Nat.add] in Wr, Vr, Ur, Wb, Vb, Ub. rewrite Nat.add_0_r in Wr, Vr, Ur, Wb, Vb, Ub.
  split; [split|].
  - cbn. split; [| exact I]. rewrite !length_app. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|]. rewrite L1.
    apply bytes_at_app. split; [exact B2|]. rewrite L2. exact B3.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [exact Wa|]. split; [lia|].
    intros k Hk. destruct (Z_lt_le_dec k (Z.of_nat n1)); [apply Wr; lia|].
    destruct (Z_lt_le_dec k (Z.of_nat n1 + Z.of_nat n2)).
    + replace (X + k) with (X + Z.of_nat n1 + (k - Z.of_nat n1)) by lia. apply Vr. lia.
    + replace (X + k) with (X + Z.of_nat n1 + Z.of_nat n2 + (k - Z.of_nat n1 - Z.of_nat n2)) by lia. apply Ur. lia.
Qed.

(* [comment removed for export] *)
Lemma repeat_sub : forall {X} (z : X) n k j, (k + j <= n)%nat -> firstn j (skipn k (repeat z n)) = repeat z j.
Proof.
  intros X z n k j H. replace n with (k + (j + (n - k - j)))%nat by (clear -H; lia).
  rewrite !repeat_app. rewrite skipn_app, repeat_length, Nat.sub_diag. cbn [skipn].
  rewrite skipn_all2 by (rewrite repeat_length; clear; lia). cbn [app].
  rewrite firstn_app, repeat_length, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  apply firstn_all2. rewrite repeat_length. clear; lia.
Qed.

Lemma rw_cells_CB_zsub : forall m X n (z : byte) k j,
  rw_cells asegs m X [CB n (repeat z n)] -> (k + j <= n)%nat -> rw_cells asegs m (X + Z.of_nat k) [CB j (repeat z j)].
Proof.
  intros m X n z k j H Hkj. pose proof (CB_u8arr _ _ _ _ H) as [ARR _].
  pose proof (u8arr_sub_CB m X _ k j ARR ltac:(rewrite repeat_length; exact Hkj)) as S.
  rewrite repeat_sub in S by exact Hkj. exact S.
Qed.

Lemma remap_range_flush : forall A L, A mod 8 = 0 ->
  remap_range A L = (rmp_pb (flush_sb A), rmp_pe (flush_se A L) - rmp_pb (flush_sb A)).
Proof.
  intros A L AM. unfold remap_range, round_up, round_down, mem_to_shadow, kPageSize, kShadowBase, rmp_pb, rmp_pe, flush_sb, flush_se.
  cbv zeta. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
  assert (E : (A + L) / 8 = A / 8 + L / 8) by (clear -AM; Z.div_mod_to_equations; lia).
  rewrite E. clear. f_equal; [| f_equal]; Z.div_mod_to_equations; lia.
Qed.

Lemma flush_hull : forall A L, A mod 8 = 0 -> flush_sb A = kShadowBase + A / 8 /\ flush_se A L = kShadowBase + A / 8 + L / 8.
Proof.
  intros A L AM. unfold flush_sb, flush_se, kShadowBase. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
  clear -AM. split; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

Section LD.
(* [comment removed for export] *)
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis LS_L0 : In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 (2^28)) L0.
Hypothesis HS_L0 : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) L0.
Hypothesis RES0_low : Forall (fun e => 0x10000 <= elo e /\ ehi e <= 0x603000) RES0.
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKuc := (ATOKu E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).

(* [comment removed for export] *)
Variables (s : aps) (a2 : astate) (sc : secchunk) (Pq : list Z) (Dq : list batch).
#[local] Notation a := (aps_alloc s).
Hypothesis PERM : Permutation (as_sec a) (as_sec a2 ++ [sc]).
Hypothesis Eres : as_residue a2 = as_residue a.
Hypothesis Ereg : forall c, get_region a2 c = get_region a c.
Hypothesis Eptr : as_ptr_committed a2 = as_ptr_committed a.
Hypothesis Enb : as_node_blocks a2 = as_node_blocks a.
Hypothesis Esb : as_store_blocks a2 = as_store_blocks a.
Hypothesis WF : AWf E0 Pq Dq a.
Hypothesis RESOK : res_ok a.
Hypothesis PTRC : as_ptr_committed a = kChunksBlockCount.
Hypothesis WF2 : exists Pq2 Dq2, AWf E0 Pq2 Dq2 a2.
#[local] Notation A := (sc_map_beg sc).
#[local] Notation L := (sc_map_size sc).

(* [comment removed for export] *)
Variables (cs : list (Z * Z)) (junk : list word) (i : nat).
Variables (ptrc na nf cur mx ga gm mu mud : Z) (nd3 : word) (TSD CTX T r0 rl : Z) (cnr : word) (shj : list byte).
Hypothesis NTH : nth_error cs i = Some (A, L).
Hypothesis CSA : forall j c', nth_error cs j = Some c' -> exists sc', In sc' (as_sec a) /\ fst c' = sc_map_beg sc' /\ snd c' = sc_map_size sc'.
Hypothesis LENCS : (Z.of_nat (length cs) + Z.of_nat (length junk) = kChunksBlockCount)%Z.
(* [comment removed for export] *)
Hypothesis RNG : Forall (fun c => 0x603000 <= fst c /\ fst c mod 4096 = 0 /\ 4096 <= snd c /\ fst c + snd c <= alloc_ceiling) cs.
Hypothesis DISJ : forall j k cj ck, nth_error cs j = Some cj -> nth_error cs k = Some ck -> j <> k ->
  fst cj + snd cj <= fst ck \/ fst ck + snd ck <= fst cj.
Hypothesis HV : 0 <= nf < 2^64 /\ 0 <= cur < 2^64 /\ 0 <= ga < 2^64 /\ 0 <= gm < 2^64.
Hypothesis HVT : 0 <= mu < 2^64 /\ 0 <= mud < 2^64.
Hypothesis HT : T = ae_thread E0.
Hypothesis HT1 : 0x5cfdd0 <= TSD. Hypothesis HT2 : TSD + 8 <= 0x603000.
(* [comment removed for export] *)
Hypothesis HC : resv_range_ok E0 r0 rl /\ r0 <= CTX /\ CTX + 160 <= r0 + rl.
Hypothesis HC4 : CTX + 4096 <= alloc_ceiling.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis HTR : placed_s T 4096.
Hypothesis HTL : forall j c', nth_error cs j = Some c' -> fst c' + snd c' <= T \/ T + 4096 <= fst c'.
Hypothesis HCL : forall j c', nth_error cs j = Some c' -> fst c' + snd c' <= CTX \/ CTX + 4096 <= fst c'.
Hypothesis DISJPA : forall j c', nth_error cs j = Some c' -> ae_ptr_array E0 + 8 * kChunksBlockCount <= fst c' \/ fst c' + snd c' <= ae_ptr_array E0.
Hypothesis HTP : ae_ptr_array E0 + 8 * kChunksBlockCount <= T \/ T + 4096 <= ae_ptr_array E0.
Hypothesis HCP : ae_ptr_array E0 + 8 * kChunksBlockCount <= CTX \/ CTX + 160 <= ae_ptr_array E0.   (* [comment removed for export] *)
#[local] Notation PA := (ae_ptr_array E0).
#[local] Notation lastc := (List.last cs (A, L)).
#[local] Notation cs' := (removelast (list_setn cs i lastc)).
#[local] Notation SH := (kShadowBase + A / 8).

(* [comment removed for export] *)
Definition ld_statics (m : mem) (cn : word) : Prop :=
  poison_globals m /\ statics m /\ rsmr_statics m cn /\ flush_statics m /\ umd_statics m.

Definition ld_static_addr (x : Z) : Prop :=
  (0xa4000 <= x < 0xaa500) \/ (0xaa800 <= x < 0x13fdd0) \/ (0x600b50 <= x < 0x600b58) \/ (0x600dd0 <= x < 0x600dd8).

Lemma ld_statics_agree : forall m m' cn,
  ld_statics m cn -> (forall x, ld_static_addr x -> m' (wa x) = m (wa x)) -> ld_statics m' cn.
Proof. aceil.
  intros m m' cn (PG & ST & RS & FS & US) AG. unfold ld_static_addr in AG.
  unfold ld_statics, poison_globals, statics, rsmr_statics, flush_statics, umd_statics,
    GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG in *.
  unfold kShadowBase, kHighMemEnd, kClearShadowMmapThreshold in *.
  destruct PG as (?&?&?&?&?&?&?). destruct ST as (?&?&?&?&?&?&?). destruct RS as (?&?&?&?&?).
  destruct FS as (?&?&?&?&?&?&?&?&?&?&?). destruct US as (?&?&?&?).
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with H : rw_cells asegs ?m0 ?A ?cs |- rw_cells asegs ?m1 ?A ?cs =>
      eapply (rw_cells_agree asegs m0 m1); [| exact H]; cbn; intros x Hx; apply AG; clear -CEILB Hx; lia end.
Qed.

(* [comment removed for export] *)
Lemma acc_ok_drop : forall Lz x,
  acc_ok Lz (aSc s) x -> (forall j, (j < snd x)%nat -> ~ sc_interior sc (bv_unsigned (acc_page x j))) -> acc_ok Lz (aSc (sA a2 s)) x.
Proof. aceil.
  intros Lz x [O|[NW IN]] HJ; [left; exact O| right]. split; [exact NW|].
  intros j Hj. apply (aS_drop_keep E0 FSB0 HR0 s a2 sc PERM Eres Esb); [apply IN; exact Hj| apply HJ; exact Hj].
Qed.

(* [comment removed for export] *)
Definition dec_us (A0 L0' : Z) (e : resp) : option (word * bool) :=
  match e with
  | mkEffectU r [] [] [] [] [] => Some (r, false)
  | mkEffectU r [] [] [u] [] [] =>
      if (bv_eqb (fst u) (Z_to_bv 64 A0) && bv_eqb (snd u) (Z_to_bv 64 L0'))%bool then Some (r, true) else None
  | _ => None
  end.

Lemma dec_us_Some : forall A0 L0' e x, dec_us A0 L0' e = Some x -> exists r u, x = (r, u) /\ e = ushape A0 L0' r u.
Proof. aceil.
  intros A0 L0' [r ws zs us cps ci] x H. unfold dec_us in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[ua un] [|]]; destruct cps; try discriminate; destruct ci; try discriminate.
  - injection H as <-. exists r, false. split; reflexivity.
  - cbn [fst snd] in H. destruct (bv_eqb ua (Z_to_bv 64 A0)) eqn:E1; [|discriminate]. destruct (bv_eqb un (Z_to_bv 64 L0')) eqn:E2; [|discriminate].
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. injection H as <-. exists r, true. split; reflexivity.
Qed.

Lemma dec_us_ushape : forall A0 L0' r u, dec_us A0 L0' (ushape A0 L0' r u) = Some (r, u).
Proof. aceil.
  intros A0 L0' r u. destruct u; unfold ushape, dec_us; cbn [fst snd]; [|reflexivity].
  rewrite !(proj2 (bv_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma u64arr_agree : forall m m' A0 ws,
  (forall x, A0 <= x < A0 + 8 * Z.of_nat (length ws) -> m' (wa x) = m (wa x)) ->
  u64arr asegs m A0 ws -> u64arr asegs m' A0 ws.
Proof. aceil.
  intros m m' A0 ws AG [(B0 & B1 & BR) (W0 & W1 & WR)]. rewrite u64s_length in B1, BR.
  split; [split; [exact B0| split; [rewrite u64s_length; exact B1|]]|].
  - rewrite u64s_length. intros k Hk. rewrite <- (BR k Hk). unfold mrd. rewrite AG by lia. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros k Hk. specialize (WR k Hk). unfold wview in *. rewrite AG by lia. exact WR.
Qed.

(* [comment removed for export] *)
Definition ld_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (mo mo' : Model) (R R' : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch ([(bv_unsigned sp - 624, bv_unsigned sp); (0xaa7c0, 0xaa7c4); (0xaa590, 0xaa599); (0xaa5a8, 0xaa5b8); (0xaa7d8, 0xaa7e8);
               (PA + 8 * Z.of_nat i, PA + 8 * Z.of_nat i + 8); (fst lastc + 24, fst lastc + 32); (T + 2888, T + 2904);
               (SH, SH + L / 8); (A, A + L)]) m m'
    /\ rw_cells asegs m' 0xaa7c0 [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs) - 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (nf + 1)); C8 (Z_to_bv 64 (cur - L)); C8 (Z_to_bv 64 mx)]
    /\ rw_cells asegs m' 0xaa7d8 [C8 (Z_to_bv 64 (ga - L)); C8 (Z_to_bv 64 (gm - L))]
    /\ u64arr asegs m' PA (upd (gws cs junk) i (Z_to_bv 64 (fst lastc)))
    /\ (forall j c', nth_error cs' j = Some c' -> exists nd, rw_cells asegs m' (fst c') [C8 (Z_to_bv 64 (fst c')); C8 (Z_to_bv 64 (snd c')); C8 nd; C8 (Z_to_bv 64 (Z.of_nat j))])
    /\ rw_cells asegs m' (T + 2888) [C8 (Z_to_bv 64 (mu + 1)); C8 (Z_to_bv 64 (mud + L))]
    /\ thread_cells m' tp TSD CTX T
    /\ ld_statics m' cnr
    /\ rw_cells asegs m' SH [CB (Z.to_nat (L / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (L / 8)))]
    /\ ATOKc R R' (sA a2 s) mo' /\ AKern E0 a2 mo'
    /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo.

Theorem ldealloc_srz :
  forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (usp lo R R' : Z) (K : TSet),
  K [] ->
  ATOKc R R' s mo -> AKern E0 a mo ->
  (* [comment removed for export] *)
  usp mod 16 = 0 -> stk asegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - 624 -> usp <= 2^47 -> mem_inv asegs m ->
  bv_unsigned tp = 0x5e0b10 ->
  rw_cells asegs m 0xaa558 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs))); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)] ->
  rw_cells asegs m 0xaa7c0 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xaa7d8 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)] ->
  u64arr asegs m PA (gws cs junk) ->
  (forall j c', nth_error cs j = Some c' -> exists nd, rw_cells asegs m (fst c') [C8 (Z_to_bv 64 (fst c')); C8 (Z_to_bv 64 (snd c')); C8 nd; C8 (Z_to_bv 64 (Z.of_nat j))]) ->
  rw_cells asegs m A [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 L); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))] ->
  thread_cells m tp TSD CTX T ->
  rw_cells asegs m (T + 2888) [C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 mud)] ->
  ld_statics m cnr ->
  rw_cells asegs m SH [CB (Z.to_nat (L / 8)) shj] ->
  (* [comment removed for export] *)
  (forall ms' mo', ld_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m mo mo' R R' ms' ->
     realizes_cfg acfg asegs (mkCfg ms' mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 (A + 4096))
                                   a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35424) fc None m (seg_rom asegs)) mo) K.
Proof. aceil.
  intros until K. intros HK TOK AK U16 SK LOC LO SPH MI TP SEC NRS SST MTX GST ARR HDRS HDRC TC TST LDS SHJ CONT.
  (* [comment removed for export] *)
  pose proof (conj HR0_ok (conj LS_L0 (conj HS_L0 RES0_low))) as SIGKEEP. clear SIGKEEP.
  (* [comment removed for export] *)
  pose proof (proj1 (Forall_forall _ _) RNG _ (nth_error_In _ _ NTH)) as (RA1 & RA2 & RA3 & RA4). cbn [fst snd] in RA1, RA2, RA3, RA4.
  pose proof (sc_geom E0 s a2 sc PERM Pq Dq WF) as (_ & APM & _ & LM4 & _ & _).
  unfold app_mem in APM. rewrite kLowAppEnd_val, kHighMemBeg_val in APM.
  assert (AHI : 0x603000 <= A) by exact RA1.
  assert (ALC : A + L <= alloc_ceiling) by exact RA4.
  assert (APL : A + L <= 0x7fff7000 \/ 0x10007fff8000 <= A) by (clear -CEILB APM; lia). clear APM.
  assert (AM8 : A mod 8 = 0) by (clear -CEILB RA2; Z.div_mod_to_equations; lia).
  assert (LM8 : L mod 8 = 0) by (clear -CEILB LM4; Z.div_mod_to_equations; lia).
  assert (HA8 : A = 8 * (A / 8)) by (clear -CEILB AM8; pose proof (Z.div_mod A 8 ltac:(lia)); lia).
  assert (HL8 : L = 8 * (L / 8)) by (clear -CEILB LM8; pose proof (Z.div_mod L 8 ltac:(lia)); lia).
  Ltac sdj := cbn; repeat split; try exact I.
  Ltac x23 H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| unfold kShadowBase].
  Ltac agx ma mb AG H := eapply (rw_cells_agree asegs ma mb); [| exact H]; cbn; intros x Hx; apply AG.
  pose proof LOC as LOC0. aceil.
  pose proof alloc_ceiling_range as CR.
  pose proof (ATOK_KIA _ _ _ _ _ _ _ _ _ _ TOK) as KIA0.
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ TOK).
  pose proof WF as WF0. destruct WF0 as (WE & _).
  (* [comment removed for export] *)
  pose proof (ptr_placed E0 FSB0 s WE ENV) as (PA0 & PA1w & _). unfold A_IMG_END in PA0. unfold kPtrArrayLen in PA1w.
  assert (PA1 : PA + 8 * 16384 <= alloc_ceiling) by (clear -CEILB PA1w; lia). clear PA1w.
  change kChunksBlockCount with 16384 in LENCS, DISJPA, HTP, HCP.
  (* [comment removed for export] *)
  pose proof (placed_s_num _ _ HTR ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & TQ4).
  assert (HTb : T + 4096 <= alloc_ceiling) by (destruct HTR as (_ & X & _); exact X).
  pose proof HC as (HCin & HCa & HCb). pose proof (resv_range_num E0 _ _ HCin ltac:(clear -HCa HCb; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  assert (INSC : In sc (as_sec a)).
  { eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. left. reflexivity. }
  assert (INCL : forall sc', In sc' (as_sec a2) -> In sc' (as_sec a)).
  { intros sc' H. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact H. }
  assert (USP : bv_unsigned (Z_to_bv 64 usp) = usp).
  { apply Z_to_bv_small. change (bv_modulus 64) with (2^64). pose proof (stk_lo_nonneg _ _ _ _ SK). lia. }
  (* [comment removed for export] *)
  set (P1 := fun x : acc => acc_ok (m_vm_lazy mo) (aSc s) x).
  assert (PSTK1 : forall x n, lo <= x -> x + Z.of_nat n <= usp -> P1 (Z_to_bv 64 x, n)).
  { intros x n H1 H2. unfold P1. apply (pol_stack E0 FSB0 HR0 s mo Pq Dq AK WF ENV0); clear -CEILB H1 H2 LOC0 SPH; lia. }
  assert (PDAT1 : forall x n, 0xa4000 <= x -> x + Z.of_nat n <= 0x603000 -> P1 (Z_to_bv 64 x, n)).
  { intros x n H1 H2. unfold P1. apply (pol_img E0 FSB0 HR0 s mo Pq Dq AK WF ENV ENV0); clear -CEILB H1 H2; lia. }
  assert (PARR1 : forall x n, PA <= x -> x + Z.of_nat n <= PA + 8 * Z.of_nat (length cs) -> P1 (Z_to_bv 64 x, n)).
  { intros x n H1 H2. unfold P1. apply (pol_ptr_head E0 FSB0 HR0 s mo Pq Dq AK WF x n PTRC); [clear -CEILB H1; lia|].
    change kPtrArrayCommit with 131072. clear -CEILB H2 LENCS. lia. }
  assert (PHDR1 : forall j c' x n, nth_error cs j = Some c' -> fst c' <= x -> x + Z.of_nat n <= fst c' + 32 -> P1 (Z_to_bv 64 x, n)).
  { intros j c' x n Hj H1 H2. unfold P1. destruct (CSA j c' Hj) as (sc' & IN' & E1 & E2).
    pose proof (proj1 (Forall_forall _ _) RNG c' (nth_error_In _ _ Hj)) as (_ & _ & R3 & _).
    apply (pol_sec_map E0 FSB0 HR0 s mo Pq Dq AK WF sc' x n IN'); rewrite <- ?E1, <- ?E2; clear -CEILB H1 H2 R3; lia. }
  (* [comment removed for export] *)
  assert (CSPL : forall j c', nth_error cs j = Some c' -> fst c' + snd c' <= 0x7fff7000 \/ 0x10007fff8000 <= fst c').
  { intros j c' Hj. destruct (CSA j c' Hj) as (sc' & IN' & E1 & E2).
    destruct WF as (_ & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
    destruct (WS3 sc' IN') as (_ & M2 & _). unfold app_mem in M2. rewrite kLowAppEnd_val, kHighMemBeg_val in M2.
    rewrite E1, E2. clear -CEILB M2. lia. }
  pose proof (ptr_placed E0 FSB0 s WE ENV) as (_ & _ & PA2). unfold A_LOWAPP_END, A_HIGH_BEG, kPtrArrayLen in PA2.
  (* [comment removed for export] *)
  set (Q1 := fun ms' : machine_state => exists (m2 : mem) (t1' a3' a4' a5' a6' a7' w3l : word),
        ms' = MS (mkR ra (Z_to_bv 64 (usp - 32)) gp tp (Z_to_bv 64 (cur - L)) t1' t2 (Z_to_bv 64 A) (Z_to_bv 64 A)
                      (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 0) a3' a4' a5' a6' a7' (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x35514) fc None m2 (seg_rom asegs)
        /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp - 32) /\ wmono asegs m m2
        /\ munch [(usp - 32, usp); (0xaa7c0, 0xaa7c4); (0xaa590, 0xaa599); (0xaa5a8, 0xaa5b8); (0xaa7d8, 0xaa7e8);
                  (PA + 8 * Z.of_nat i, PA + 8 * Z.of_nat i + 8); (fst lastc + 24, fst lastc + 32)] m m2
        /\ rw_cells asegs m2 (usp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells asegs m2 0xaa7c0 [C4 (Z_to_bv 64 0)]
        /\ rw_cells asegs m2 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs) - 1)); C1 (Z_to_bv 8 0)]
        /\ rw_cells asegs m2 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (nf + 1)); C8 (Z_to_bv 64 (cur - L)); C8 (Z_to_bv 64 mx)]
        /\ rw_cells asegs m2 0xaa7d8 [C8 (Z_to_bv 64 (ga - L)); C8 (Z_to_bv 64 (gm - L))]
        /\ u64arr asegs m2 PA (upd (gws cs junk) i (Z_to_bv 64 (fst lastc)))
        /\ rw_cells asegs m2 A [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 L); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))]
        /\ rw_cells asegs m2 (fst lastc) [C8 (Z_to_bv 64 (fst lastc)); C8 (Z_to_bv 64 (snd lastc)); C8 w3l; C8 (Z_to_bv 64 (Z.of_nat i))]).
  pose proof (nth_error_lt _ _ _ NTH) as LTI.
  assert (NE : cs <> []) by (destruct cs; [destruct i; discriminate| discriminate]).
  pose proof (last_nth cs (A, L) NE) as NL.
  pose proof (proj1 (Forall_forall _ _) RNG _ (nth_error_In _ _ NL)) as (RL1' & RL2' & RL3' & RL4'). aceil. pose proof (CSPL _ _ NL) as RL5'.
  pose proof (DISJPA _ _ NL) as DPL'.
  assert (PH1 : evtA asegs P1 Q1 (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 (A + 4096))
                                   a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35424) fc None m (seg_rom asegs))).
  { eapply (ldpre_A P1 ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Q1 m lo PA cs junk i (A, L)
                           ptrc na nf cur mx ga gm nd3);
      [ rewrite USP; exact SK | exact LOC0 | rewrite USP; clear -CEILB LO; lia | rewrite USP; exact SPH | exact MI | exact NTH
      | exact SEC | exact NRS | exact SST | exact MTX | exact GST | exact ARR | clear -CEILB PA0 PA1 LENCS; lia | exact HDRS | exact HDRC
      | exact RNG
      | exact DISJ | intros j c' Hj; pose proof (DISJPA j c' Hj); clear -CEILB H LENCS; lia | exact HV
      | rewrite USP; exact PSTK1 | exact PDAT1 | exact PARR1 | exact PHDR1 | ].
    cbn [fst snd].
    intros m1 t1x MI1 SK1 WM1 MU1 FR1 MTX1 NRS1 SST1 GST1 ARR1 HDRC1.
    destruct (Nat.eq_dec (Datatypes.S i) (length cs)) as [EQL|NEL].
    + assert (LC : List.last cs (A, L) = (A, L)) by (eapply last_of_nth; [exact NTH| exact EQL]).
      unfold AF_ldealloc1.lastc in ARR1 |- *. rewrite LC in ARR1 |- *. cbn [fst snd] in ARR1 |- *.
      eapply ldpre_B1 with (c := (A, L)) (cs := cs) (i := i) (PA := PA) (junk := junk) (lo := lo) (Q := Q1) (P := P1)
         (nf := nf) (cur := cur) (ga := ga) (gm := gm) (nd3 := nd3) (m := m);
        [ exact NTH | clear -CEILB PA0 PA1 LENCS; lia | exact HDRS
        | exact RNG
        | exact DISJ | intros j c' Hj; pose proof (DISJPA j c' Hj); clear -CEILB H LENCS; lia | exact HV
        | exact PDAT1 | exact PARR1 | exact PHDR1 | exact EQL | exact MI1 | exact SK1 | exact MTX1 | exact GST1 | exact HDRC1 | ].
      cbn [fst snd]. intros m2 a3' a4' a5' a6' a7' t1' MI2 SK2 WM2 MU2 MTX2 GST2 HDRC2.
      apply evtA_done. unfold Q1. exists m2, t1', a3', a4', a5', a6', a7', nd3.
      rewrite LC. cbn [fst snd]. rewrite USP in SK2, FR1, MU1 |- *.
      split; [reflexivity|]. split; [exact MI2|]. split; [exact SK2|]. split; [eapply wmono_trans; [exact WM1| exact WM2]|].
      split. { eapply munch_trans.
               - eapply munch_weaken; [| exact MU1]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia.
               - eapply munch_weaken; [| exact MU2]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia. }
      pose proof (DISJPA i (A, L) NTH) as DPA. cbn [fst snd] in DPA.
      split. { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. clear -CEILB LO LOC ALC RA3. sdj; lia. }
      split; [exact MTX2|].
      split. { eapply rw_cells_transport; [exact NRS1| exact MU2| exact WM2|]. clear -CEILB AHI. sdj; lia. }
      split. { eapply rw_cells_transport; [exact SST1| exact MU2| exact WM2|]. clear -CEILB AHI. sdj; lia. }
      split; [exact GST2|].
      split. { eapply u64arr_transport; [exact ARR1| exact MU2| exact WM2|].
               assert (LU : length (upd (gws cs junk) i (Z_to_bv 64 A)) = (length cs + length junk)%nat).
               { rewrite upd_length. unfold gws. rewrite length_app, length_map. reflexivity. }
               rewrite LU. clear -CEILB DPA PA0 LENCS AHI RA3. sdj; lia. }
      split; [exact HDRC2| exact HDRC2].
    + (* [comment removed for export] *)
      destruct (HDRS _ _ NL) as [w3l LST].
      pose proof DPL' as DPL. pose proof RL1' as RL1. pose proof RL3' as RL3. pose proof RL4' as RL4.
      replace (Z.of_nat (length cs - 1)) with (Z.of_nat (length cs) - 1) in LST by (clear -CEILB LTI; lia).
      rewrite USP in MU1.
      assert (LST1 : rw_cells asegs m1 (fst lastc) [C8 (Z_to_bv 64 (fst lastc)); C8 (Z_to_bv 64 (snd lastc)); C8 w3l; C8 (Z_to_bv 64 (Z.of_nat (length cs) - 1))]).
      { eapply rw_cells_transport; [exact LST| exact MU1| exact WM1|]. clear -CEILB LO LOC RL1 RL3 RL4 DPL PA0 LENCS LTI. sdj; lia. }
      eapply ldpre_B2 with (c := (A, L)) (cs := cs) (i := i) (PA := PA) (junk := junk) (lo := lo) (Q := Q1) (P := P1)
         (nf := nf) (cur := cur) (ga := ga) (gm := gm) (nd3 := nd3) (m := m);
        [ exact NTH | clear -CEILB PA0 PA1 LENCS; lia | exact HDRS
        | exact RNG
        | exact DISJ | intros j c' Hj; pose proof (DISJPA j c' Hj); clear -CEILB H LENCS; lia | exact HV
        | exact PDAT1 | exact PARR1 | exact PHDR1 | clear -CEILB NEL LTI; lia | exact MI1 | exact SK1 | exact MTX1 | exact GST1 | exact HDRC1 | exact LST1 | ].
      cbn [fst snd]. intros m2 a3' a4' a5' a6' a7' t1' MI2 SK2 WM2 MU2 MTX2 GST2 HDRC2 LST2.
      apply evtA_done. unfold Q1. exists m2, t1', a3', a4', a5', a6', a7', w3l.
      unfold AF_ldealloc1.lastc in MU2, LST2 |- *. rewrite USP in SK2, FR1 |- *.
      split; [reflexivity|]. split; [exact MI2|]. split; [exact SK2|]. split; [eapply wmono_trans; [exact WM1| exact WM2]|].
      split. { eapply munch_trans.
               - eapply munch_weaken; [| exact MU1]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia.
               - eapply munch_weaken; [| exact MU2]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia. }
      pose proof (DISJPA i (A, L) NTH) as DPA. cbn [fst snd] in DPA.
      split. { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. clear -CEILB LO LOC RL1 RL3 RL4. sdj; lia. }
      split; [exact MTX2|].
      split. { eapply rw_cells_transport; [exact NRS1| exact MU2| exact WM2|]. clear -CEILB RL1. sdj; lia. }
      split. { eapply rw_cells_transport; [exact SST1| exact MU2| exact WM2|]. clear -CEILB RL1. sdj; lia. }
      split; [exact GST2|].
      split. { eapply u64arr_transport; [exact ARR1| exact MU2| exact WM2|].
               rewrite upd_length. unfold gws. rewrite length_app, length_map. clear -CEILB DPL PA0 LENCS RL1 RL3. sdj; lia. }
      split; [exact HDRC2| exact LST2]. }
  eapply (srzA_seg asegs (aSc s) (aNc s) (aEBc s) P1 Q1); [exact PH1| split; [exact KIA0| intros x Hx; exact Hx] |].
  clear PH1. intros ms1 mo1 HQ1 AG1 [KIA1 _].
  destruct HQ1 as (m2 & t1' & a3' & a4' & a5' & a6' & a7' & w3l & -> & MI2 & SK2 & WM2 & MU2 & FR2 & MTX2 & NRS2 & SST2 & GST2 & ARR2 & HDRC2 & LST2).
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG1 KIA1) as TOK1.
  pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
  pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 AK) as AK1.
  assert (LDS2 : ld_statics m2 cnr).
  { apply (ld_statics_agree m m2 cnr LDS). intros x Hx. unfold ld_static_addr in Hx. apply MU2.
    rewrite wa_unsigned by (clear -CEILB Hx; lia). clear -CEILB Hx LOC LO PA0 RL1'. sdj; lia. }
  assert (TC2 : thread_cells m2 tp TSD CTX T).
  { destruct TC as (X1 & X2 & X3 & X4 & X5).
    unfold thread_cells. Ltac tcx X MU WM := eapply rw_cells_transport; [exact X| exact MU| exact WM|].
    split; [tcx X1 MU2 WM2| split; [tcx X2 MU2 WM2| split; [tcx X3 MU2 WM2| split; [tcx X4 MU2 WM2| tcx X5 MU2 WM2]]]];
      pose proof (HCL _ _ NL) as Y1; pose proof HCP as Y2; pose proof (HTL _ _ NL) as Y3; pose proof HTP as Y4;
      clear -CEILB LOC LO PA0 RL1' RL3' TP HT1 HT2 HCa HCb CQ1 CQ2 CQ3 TQ1 TQ2 TQ3 HTb Y1 Y2 Y3 Y4 LENCS LTI; sdj; lia. }
  assert (TST2 : rw_cells asegs m2 (T + 2888) [C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 mud)]).
  { eapply rw_cells_transport; [exact TST| exact MU2| exact WM2|].
    pose proof (HTL _ _ NL) as Y1. pose proof HTP as Y2. change kChunksBlockCount with 16384 in Y2.
    pose proof TQ1 as Y3. pose proof HTb as Y4. pose proof TQ3 as Y5.
    clear -CEILB LOC LO PA0 RL1' RL3' Y3 Y4 Y5 Y1 Y2 LENCS LTI. sdj; lia. }
  assert (SHJ2 : rw_cells asegs m2 SH [CB (Z.to_nat (L / 8)) shj]).
  { eapply rw_cells_transport; [exact SHJ| exact MU2| exact WM2|]. unfold kShadowBase. clear -CEILB LOC LO PA0 PA1 PA2 LENCS LTI RL1' RL3' RL4' RL5' AHI ALC RA3 HL8. sdj; lia. }
  assert (USP2 : bv_unsigned (Z_to_bv 64 (usp - 32)) = usp - 32).
  { apply Z_to_bv_small. change (bv_modulus 64) with (2^64). clear -CEILB LOC LO SPH. lia. }
  (* [comment removed for export] *)
  assert (TRX : forall (mX mY : mem), wmono asegs mX mY -> munch [(usp - 32 - 64, usp - 32); (SH, SH + L / 8)] mX mY ->
    rw_cells asegs mX (usp - 32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mX 0xaa7c0 [C4 (Z_to_bv 64 0)] ->
    rw_cells asegs mX 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs) - 1)); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs mX 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (nf + 1)); C8 (Z_to_bv 64 (cur - L)); C8 (Z_to_bv 64 mx)] ->
    rw_cells asegs mX 0xaa7d8 [C8 (Z_to_bv 64 (ga - L)); C8 (Z_to_bv 64 (gm - L))] ->
    u64arr asegs mX PA (upd (gws cs junk) i (Z_to_bv 64 (fst lastc))) ->
    rw_cells asegs mX A [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 L); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))] ->
    rw_cells asegs mX (fst lastc) [C8 (Z_to_bv 64 (fst lastc)); C8 (Z_to_bv 64 (snd lastc)); C8 w3l; C8 (Z_to_bv 64 (Z.of_nat i))] ->
    thread_cells mX tp TSD CTX T ->
    rw_cells asegs mX (T + 2888) [C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 mud)] ->
    ld_statics mX cnr ->
       rw_cells asegs mY (usp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs mY 0xaa7c0 [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs mY 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs) - 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs mY 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (nf + 1)); C8 (Z_to_bv 64 (cur - L)); C8 (Z_to_bv 64 mx)]
    /\ rw_cells asegs mY 0xaa7d8 [C8 (Z_to_bv 64 (ga - L)); C8 (Z_to_bv 64 (gm - L))]
    /\ u64arr asegs mY PA (upd (gws cs junk) i (Z_to_bv 64 (fst lastc)))
    /\ rw_cells asegs mY A [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 L); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))]
    /\ rw_cells asegs mY (fst lastc) [C8 (Z_to_bv 64 (fst lastc)); C8 (Z_to_bv 64 (snd lastc)); C8 w3l; C8 (Z_to_bv 64 (Z.of_nat i))]
    /\ thread_cells mY tp TSD CTX T
    /\ rw_cells asegs mY (T + 2888) [C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 mud)]
    /\ ld_statics mY cnr).
  { intros mX mY WMx MUx FRx MTXx NRSx SSTx GSTx ARRx HDRCx LSTx TCx TSTx LDSx.
    split. { x23 FRx MUx WMx. clear -CEILB LOC LO AHI ALC APL RA3 HL8. sdj; lia. }
    split. { x23 MTXx MUx WMx. clear -CEILB LOC LO AHI. sdj; lia. }
    split. { x23 NRSx MUx WMx. clear -CEILB LOC LO AHI. sdj; lia. }
    split. { x23 SSTx MUx WMx. clear -CEILB LOC LO AHI. sdj; lia. }
    split. { x23 GSTx MUx WMx. clear -CEILB LOC LO AHI. sdj; lia. }
    split. { eapply u64arr_transport; [exact ARRx| exact MUx| exact WMx|]. rewrite upd_length. unfold gws. rewrite length_app, length_map.
             unfold kShadowBase. clear -CEILB LOC LO PA0 PA1 PA2 LENCS AHI ALC APL RA3 HL8. sdj; lia. }
    split. { x23 HDRCx MUx WMx. clear -CEILB LOC LO AHI ALC APL RA3 HL8. sdj; lia. }
    split. { x23 LSTx MUx WMx. clear -CEILB LOC LO RL1' RL4' RL3' RL5' AHI ALC APL RA3 HL8. sdj; lia. }
    split. { destruct TCx as (X1 & X2 & X3 & X4 & X5). unfold thread_cells.
             split; [x23 X1 MUx WMx| split; [x23 X2 MUx WMx| split; [x23 X3 MUx WMx| split; [x23 X4 MUx WMx| x23 X5 MUx WMx]]]];
               clear -CEILB LOC LO TP HT1 HT2 CQ1 CQ2 CQ3 CQ4 HCa HCb AHI ALC APL RA3 HL8; sdj; lia. }
    split. { x23 TSTx MUx WMx. clear -CEILB LOC LO TQ1 TQ3 TQ4 HTb AHI ALC APL RA3 HL8. sdj; lia. }
    apply (ld_statics_agree mX mY cnr LDSx). intros x Hx. unfold ld_static_addr in Hx. apply MUx.
    rewrite wa_unsigned by (clear -CEILB Hx; lia). unfold kShadowBase. clear -CEILB Hx LOC LO AHI. sdj; lia. }
  (* [comment removed for export] *)
  assert (PH3b : forall (m3 : mem) (mo3 : Model) (rax t0' t1'' t2' a0' a1' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' : word),
    mem_inv asegs m3 -> stk asegs m3 lo (usp - 32) -> wmono asegs m m3 ->
    munch [(usp - 624, usp); (0xaa7c0, 0xaa7c4); (0xaa590, 0xaa599); (0xaa5a8, 0xaa5b8); (0xaa7d8, 0xaa7e8);
           (PA + 8 * Z.of_nat i, PA + 8 * Z.of_nat i + 8); (fst lastc + 24, fst lastc + 32); (SH, SH + L / 8)] m m3 ->
    rw_cells asegs m3 (usp - 32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m3 0xaa7c0 [C4 (Z_to_bv 64 0)] ->
    rw_cells asegs m3 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs) - 1)); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m3 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (nf + 1)); C8 (Z_to_bv 64 (cur - L)); C8 (Z_to_bv 64 mx)] ->
    rw_cells asegs m3 0xaa7d8 [C8 (Z_to_bv 64 (ga - L)); C8 (Z_to_bv 64 (gm - L))] ->
    u64arr asegs m3 PA (upd (gws cs junk) i (Z_to_bv 64 (fst lastc))) ->
    rw_cells asegs m3 A [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 L); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))] ->
    rw_cells asegs m3 (fst lastc) [C8 (Z_to_bv 64 (fst lastc)); C8 (Z_to_bv 64 (snd lastc)); C8 w3l; C8 (Z_to_bv 64 (Z.of_nat i))] ->
    thread_cells m3 tp TSD CTX T ->
    rw_cells asegs m3 (T + 2888) [C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 mud)] ->
    ld_statics m3 cnr ->
    rw_cells asegs m3 SH [CB (Z.to_nat (L / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (L / 8)))] ->
    ATOKuc R R' (sA a2 s) A L mo3 -> AKern E0 a mo3 ->
    m_fs mo3 = m_fs mo /\ m_fds mo3 = m_fds mo /\ m_tid mo3 = m_tid mo ->
    realizes_cfg acfg asegs (mkCfg (MS (mkR rax (Z_to_bv 64 (usp - 32)) gp tp t0' t1'' t2' (Z_to_bv 64 A) (Z_to_bv 64 A)
                                    a0' a1' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (Z_to_bv 64 0x35524) fc None m3 (seg_rom asegs)) mo3) K).
  { clear SK MI SEC NRS SST MTX GST ARR HDRC TC TST LDS SHJ.
    intros m3 mo3 rax t0' t1'' t2' a0' a1' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' MI3 SK3 WM3 MU3 FR3 MTX3 NRS3 SST3 GST3 ARR3 HDRC3 LST3 TC3 TST3 LDS3 ZSH3 TOKu3 AK3 (Ffs3 & Ffds3 & Ftid3).
    assert (ENV2 : ENVOK E0 FSB0 (sA a2 s)) by (destruct TOKu3 as (_ & _ & E & _); exact E).
    destruct WF2 as (Pq2 & Dq2 & WFa2).
    assert (AK3b : AKern E0 a2 mo3) by (exact (AKern_sec_incl E0 a a2 mo3 AK3 INCL Ereg Eptr Enb Esb)).
    (* [comment removed for export] *)
    set (P3 := fun x : acc => acc_ok (m_vm_lazy mo3) (aSc (sA a2 s)) x).
    assert (PSTK3 : forall x n, lo <= x -> x + Z.of_nat n <= usp -> P3 (Z_to_bv 64 x, n)).
    { intros x n H1 H2. unfold P3. apply (pol_stack E0 FSB0 HR0 (sA a2 s) mo3 Pq2 Dq2 AK3b WFa2 ENV0); clear -CEILB H1 H2 LOC0 SPH; lia. }
    assert (PSTK3' : forall x n, lo <= x -> x + Z.of_nat n <= usp - 32 -> P3 (Z_to_bv 64 x, n)) by (intros; apply PSTK3; lia).
    assert (PDAT3 : forall x n, 0xa4000 <= x -> x + Z.of_nat n <= 0x603000 -> P3 (Z_to_bv 64 x, n)).
    { intros x n H1 H2. unfold P3. apply (pol_img E0 FSB0 HR0 (sA a2 s) mo3 Pq2 Dq2 AK3b WFa2 ENV2 ENV0); clear -CEILB H1 H2; lia. }
    assert (PT3 : forall x n, T <= x -> x + Z.of_nat n <= T + 4096 -> P3 (Z_to_bv 64 x, n)).
    { intros x n H1 H2. unfold P3. apply (pol_thread E0 FSB0 HR0 (sA a2 s) mo3 Pq2 Dq2 AK3b WFa2); rewrite <- HT; assumption. }
    assert (PCTX3 : P3 (Z_to_bv 64 (CTX + 152), 8%nat)).
    { unfold P3. apply (pol_resv_range E0 FSB0 HR0 (sA a2 s) mo3 AK3b r0 rl); [exact HCin| clear -CEILB HCa; lia| clear -CEILB HCb; cbn; lia]. }
    assert (PHC3 : forall x n, A <= x -> x + Z.of_nat n <= A + 32 -> P3 (Z_to_bv 64 x, n)).
    { intros x n H1 H2. unfold P3. pose proof (proj2 (ak_sec _ _ _ AK3 sc INSC)) as EG.
      eapply (acc_ok_of_lazy_disjoint mo3 (aSc (sA a2 s)) A (A + L)); [apply eager_rw_lazy_disjoint; exact EG| clear -CEILB AHI; lia| clear -CEILB ALC; lia| exact H1| clear -CEILB H2 RA3; lia]. }
    (* [comment removed for export] *)
    set (Q3 := fun ms' : machine_state => exists (m4 : mem) (t0x t1x t2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word),
          ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0x t1x t2x s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 0) a3x a4x a5x a6x a7x
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6x) F (Z_to_bv 64 0x6746c) fc None m4 (seg_rom asegs)
          /\ mem_inv asegs m4 /\ stk asegs m4 lo usp /\ wmono asegs m3 m4
          /\ munch [(usp - 96, usp); (T + 2888, T + 2904)] m3 m4
          /\ rw_cells asegs m4 (T + 2888) [C8 (Z_to_bv 64 (mu + 1)); C8 (Z_to_bv 64 (mud + L))]
          /\ rw_cells asegs m4 A [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 L); C8 nd3; C8 (Z_to_bv 64 (Z.of_nat i))]
          /\ thread_cells m4 tp TSD CTX T).
    assert (PH3 : evtA asegs P3 Q3 (MS (mkR rax (Z_to_bv 64 (usp - 32)) gp tp t0' t1'' t2' (Z_to_bv 64 A) (Z_to_bv 64 A)
                                    a0' a1' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (Z_to_bv 64 0x35524) fc None m3 (seg_rom asegs))).
    { eapply ldtail_walk with (lo := lo) (A := A) (L := L) (nd3 := nd3) (ix := Z_to_bv 64 (Z.of_nat i)) (TSD := TSD) (CTX := CTX) (T := T)
                              (mu := mu) (mud := mud) (s0c := s0) (s1c := s1) (s2c := s2) (rac := ra) (Q := Q3) (m := m3);
        rewrite ?USP2;
        [ exact SK3 | exact LOC0 | clear -CEILB LO; lia | clear -CEILB SPH; lia | exact MI3 | exact FR3
        | clear -CEILB AHI ALC RA3; lia | exact HDRC3 | exact TC3 | exact HT1 | exact HT2
        | clear -CEILB CQ1 HCa; lia | exact HC4 | exact (conj TQ1 TQ3) | exact HTb | rewrite TP; clear; lia
        | exact TST3
        | pose proof (HTL _ _ NTH) as Y; cbn [fst snd] in Y; clear -CEILB Y RA3; lia
        | pose proof (HCL _ _ NTH) as Y; cbn [fst snd] in Y; clear -CEILB Y RA3; lia
        | exact HTC
        | intros x n H1 H2; apply PSTK3; [exact H1| clear -CEILB H2; lia] | exact PDAT3 | exact PCTX3 | exact PT3 | exact PHC3 | ].
      intros m4 a3y a4y t0y t1y t2y a5y a6y a7y t3y t4y t5y t6y MI4 SK4 WM4 MU4 TST4 HDRC4 TC4.
      apply evtA_done. unfold Q3. exists m4. do 12 eexists.
      rewrite ?USP2 in SK4, MU4 |- *. replace (usp - 32 + 32) with usp in SK4 |- * by lia.
      split; [reflexivity|]. split; [exact MI4|]. split; [exact SK4|]. split; [exact WM4|].
      split. { eapply munch_weaken; [| exact MU4]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia. }
      split; [exact TST4|]. split; [exact HDRC4| exact TC4]. }
    eapply (srzA_seg asegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s) + L) P3 Q3);
      [exact PH3| split; [exact (ATOKu_KIA _ _ _ _ _ _ _ _ _ _ _ _ TOKu3)| intros x Hx; exact Hx] |].
    clear PH3. intros ms4 mo4 HQ4 AG4 [KIA4 _].
    destruct HQ4 as (m4 & t0x & t1x & t2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & -> & MI4 & SK4 & WM4 & MU4 & TST4 & HDRC4 & TC4).
    pose proof (ATOKu_magree _ _ _ _ _ _ _ _ _ _ _ _ _ TOKu3 AG4 KIA4) as TOKu4.
    pose proof (magree_frame _ _ AG4) as (Ffds4 & Fvm4 & Flz4 & Ffs4 & Fh4 & Ftid4 & _).
    pose proof (AKern_frame _ _ _ _ Fvm4 Flz4 AK3) as AK4.
    assert (LDS4 : ld_statics m4 cnr).
    { apply (ld_statics_agree m3 m4 cnr LDS3). intros x Hx. unfold ld_static_addr in Hx. apply MU4.
      rewrite wa_unsigned by (clear -CEILB Hx; lia). clear -CEILB Hx LOC LO TQ1 TQ3 TQ4. sdj; lia. }
    (* [comment removed for export] *)
    set (P4 := fun x : acc => exists y n, x = (Z_to_bv 64 y, n) /\ ((lo <= y /\ y + Z.of_nat n <= usp) \/ (0xa4000 <= y /\ y + Z.of_nat n <= 0x603000))).
    assert (P4pol : forall moX, AKern E0 a2 moX -> forall x, P4 x -> acc_ok (m_vm_lazy moX) (aSc (sA a2 s)) x).
    { intros moX AKX x (y & n & -> & [[H1 H2]|[H1 H2]]).
      - apply (pol_stack E0 FSB0 HR0 (sA a2 s) moX Pq2 Dq2 AKX WFa2 ENV0); clear -CEILB H1 H2 LOC0 SPH; lia.
      - apply (pol_img E0 FSB0 HR0 (sA a2 s) moX Pq2 Dq2 AKX WFa2 ENV2 ENV0); clear -CEILB H1 H2; lia. }
    assert (AK4b : AKern E0 a2 mo4) by (exact (AKern_sec_incl E0 a a2 mo4 AK4 INCL Ereg Eptr Enb Esb)).
    eapply (rzA_mm_cfg asegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s) + L) P4 (NMunmap A L) (munmap_CHK A L) (dec_us A L)
              (umd_post (fun x r u => x = (r, u)) ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L lo m4) _ mo4 K).
    - unfold munmap_CHK. apply mm_node_munmap.
    - right. intros; reflexivity.
    - eapply (unmap_or_die_specA P4); rewrite ?USP.
      + intros y n H1 H2. exists y, n. split; [reflexivity| right; split; assumption].
      + intros rsp x D. destruct (dec_us_Some _ _ _ _ D) as (r & u & -> & ->). exists r, u. split; reflexivity.
      + exact SK4.
      + exact LOC0.
      + clear -CEILB LO; lia.
      + exact SPH.
      + exact MI4.
      + exact (proj2 (proj2 (proj2 (proj2 LDS4)))).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + unfold a_image_end. clear -CEILB AHI. lia.
      + clear -CEILB RA3. lia.
      + clear -CEILB ALC LOC. lia.
      + intros y n H1 H2. exists y, n. split; [reflexivity| left; split; assumption].
    - split; [exact (ATOKu_KIA _ _ _ _ _ _ _ _ _ _ _ _ TOKu4)| exact (P4pol mo4 AK4b)].
    - exact HK.
    - intros mo5 AG5 KIA5.
      destruct (ev_munmap E0 FSB0 HR0 L0 RES0 EB0 ENV0 s a2 sc PERM Ereg Eptr Enb Esb ltac:(clear -CEILB RA3; lia) R R' mo4 mo5 Pq Dq TOKu4 AK4 WF AG5 KIA5)
        as (NU & GR & ALL).
      split; [exact NU|]. split; [exact GR|].
      intros eff mo' HC' NR'. destruct (ALL eff mo' HC' NR') as (ANS & -> & -> & TOK6 & AK6).
      exists (Z_to_bv 64 0, true). split. { change (dec_us A L (ushape A L (Z_to_bv 64 0) true) = Some (Z_to_bv 64 0, true)). apply dec_us_ushape. }
      exists (aSc (sA a2 s)), (aNc (sA a2 s)), (aEBc (sA a2 s)).
      split; [exact (ATOK_LI _ _ _ _ _ _ _ _ _ _ TOK6)|]. split; [exact (P4pol _ AK6)|].
      intros ms7 mo7 HQ7 AG7 KIA7 PS7.
      destruct HQ7 as (r & u & RG' & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m7 & E & MU7 & WMu & MI7 & SK7 & US7 & HR7).
      injection HR7 as <- <-. change (is_err (Z_to_bv 64 0)) with false in E. cbv iota in E. subst ms7.
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK6 AG7 KIA7) as TOK7.
      pose proof (magree_frame _ _ AG5) as (Ffds5 & Fvm5 & Flz5 & Ffs5 & Fh5 & Ftid5 & _).
      pose proof (magree_frame _ _ AG7) as (Ffds7 & Fvm7 & Flz7 & Ffs7 & Fh7 & Ftid7 & _).
      pose proof (AKern_frame _ _ _ _ Fvm7 Flz7 AK6) as AK7.
      rewrite USP in MU7, SK7.
      assert (MU37 : munch [(usp - 96, usp); (T + 2888, T + 2904); (A, A + L)] m3 m7).
      { eapply munch_trans.
        - eapply munch_weaken; [| exact MU4]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia.
        - eapply munch_weaken; [| exact MU7]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia. }
      assert (AG37 : forall x, 0 <= x < 2^64 -> ~ (usp - 96 <= x < usp) -> ~ (T + 2888 <= x < T + 2904) -> ~ (A <= x < A + L) -> m7 (wa x) = m3 (wa x)).
      { intros x H0 H1 H2 H3. apply MU37. rewrite wa_unsigned by exact H0. cbn. clear -CEILB H1 H2 H3. tauto. }
      apply CONT. unfold ld_post. rewrite ?USP.
      exists q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10. exists q11, q12, q13, q14, m7.
      split; [reflexivity|]. split; [exact MI7|]. split; [exact SK7|].
      split. { eapply munch_trans; [| eapply munch_trans].
               - eapply munch_weaken; [| exact MU3]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia.
               - eapply munch_weaken; [| exact MU4]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia.
               - eapply munch_weaken; [| exact MU7]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia. }
      split. { agx m3 m7 AG37 MTX3; clear -CEILB Hx LOC LO TQ1 TQ3 TQ4 AHI; lia. }
      split. { agx m3 m7 AG37 NRS3; clear -CEILB Hx LOC LO TQ1 TQ3 TQ4 AHI; lia. }
      split. { agx m3 m7 AG37 SST3; clear -CEILB Hx LOC LO TQ1 TQ3 TQ4 AHI; lia. }
      split. { agx m3 m7 AG37 GST3; clear -CEILB Hx LOC LO TQ1 TQ3 TQ4 AHI; lia. }
      split. { eapply (u64arr_agree m3 m7); [| exact ARR3]. rewrite upd_length. unfold gws. rewrite length_app, length_map.
               intros x Hx. pose proof HTP as Y2. pose proof (DISJPA _ _ NTH) as Y3. cbn [fst snd] in Y3.
               apply AG37; clear -CEILB Hx LOC LO TQ1 TQ3 TQ4 PA0 PA1 LENCS Y2 Y3 RA3; lia. }
      split. { intros j c' Hj. apply nth_error_removelast in Hj as [Hj LJ]. rewrite length_list_setn in LJ.
               apply nth_error_list_setn in Hj as [[-> ->]|[NEQ Hj]].
               - exists w3l. unfold AF_ldealloc1.lastc in LST3 |- *.
                 assert (NEL : i <> (length cs - 1)%nat) by (clear -CEILB LJ; lia).
                 pose proof (DISJ _ _ _ _ NTH NL NEL) as D1. cbn [fst snd] in D1. pose proof (HTL _ _ NL) as D2.
                 agx m3 m7 AG37 LST3; clear -CEILB Hx LOC LO RL1' RL3' RL4' RA3 D1 D2 TQ1 TQ3 TQ4; lia.
               - destruct (HDRS _ _ Hj) as [nd HD]. exists nd.
                 pose proof (proj1 (Forall_forall _ _) RNG _ (nth_error_In _ _ Hj)) as (Q1' & Q2' & Q3' & Q4'). pose proof (CSPL _ _ Hj) as Q5'.
                 aceil.
                 pose proof (DISJ _ _ _ _ Hj NTH NEQ) as D1. cbn [fst snd] in D1.
                 assert (NEL : j <> (length cs - 1)%nat) by (clear -CEILB LJ; lia).
                 pose proof (DISJ _ _ _ _ Hj NL NEL) as D2. pose proof (HTL _ _ Hj) as D3. pose proof (DISJPA _ _ Hj) as D4.
                 assert (HD3 : rw_cells asegs m3 (fst c') [C8 (Z_to_bv 64 (fst c')); C8 (Z_to_bv 64 (snd c')); C8 nd; C8 (Z_to_bv 64 (Z.of_nat j))]).
                 { x23 HD MU3 WM3. unfold AF_ldealloc1.lastc. clear -CEILB LOC LO Q1' Q3' Q4' Q5' D2 D4 PA0 LENCS LTI RL3' AHI ALC APL RA3 HL8. sdj; lia. }
                 agx m3 m7 AG37 HD3; clear -CEILB Hx LOC LO Q1' Q3' Q4' D1 D3 RA3 TQ1 TQ3 TQ4; lia. }
      split. { eapply (rw_cells_agree asegs m4 m7); [| exact TST4]. cbn. intros x Hx. apply MU7. rewrite wa_unsigned by (clear -CEILB Hx TQ1 HTb; lia). cbn.
               pose proof (HTL _ _ NTH) as Y1. cbn [fst snd] in Y1. clear -CEILB Hx LOC LO TQ1 HTb Y1 RA3. lia. }
      split. { destruct TC4 as (X1 & X2 & X3 & X4 & X5). unfold thread_cells.
               pose proof (HCL _ _ NTH) as Y1. cbn [fst snd] in Y1.
               assert (AG47 : forall x, 0 <= x < 2^64 -> ~ (usp - 64 <= x < usp) -> ~ (A <= x < A + L) -> m7 (wa x) = m4 (wa x)).
               { intros x H0 H1 H2. apply MU7. rewrite wa_unsigned by exact H0. cbn. clear -CEILB H1 H2. tauto. }
               split; [agx m4 m7 AG47 X1| split; [agx m4 m7 AG47 X2| split; [agx m4 m7 AG47 X3| split; [agx m4 m7 AG47 X4| agx m4 m7 AG47 X5]]]];
                 clear -CEILB Hx LOC LO TP HT1 HT2 CQ1 CQ2 CQ3 HCa HCb TQ1 TQ3 TQ4 HTb Y1 RA3 AHI; lia. }
      split. { apply (ld_statics_agree m4 m7 cnr LDS4). intros x Hx. unfold ld_static_addr in Hx. apply MU7.
               rewrite wa_unsigned by (clear -CEILB Hx; lia). cbn. clear -CEILB Hx LOC LO AHI TQ1 TQ3 TQ4. lia. }
      split. { agx m3 m7 AG37 ZSH3; unfold kShadowBase in Hx; rewrite ?repeat_length in Hx; clear -CEILB Hx LOC LO TQ1 TQ3 TQ4 HTb AHI ALC APL RA3 HL8; lia. }
      split; [exact TOK7|]. split; [exact AK7|].
      assert (UF : m_fs (m_unmap mo5 A L) = m_fs mo5 /\ m_fds (m_unmap mo5 A L) = m_fds mo5 /\ m_tid (m_unmap mo5 A L) = m_tid mo5) by (repeat split; reflexivity).
      destruct UF as (U1 & U2 & U3). rewrite Ffs7, Ffds7, Ftid7, U1, U2, U3, Ffs5, Ffds5, Ftid5, Ffs4, Ffds4, Ftid4, Ffs3, Ffds3, Ftid3.
      repeat split; reflexivity. }
  (* [comment removed for export] *)
  assert (APLp : A + L <= 0x7fff7000 \/ (kHighMemBeg <= A /\ (kHighMemBeg + 8 <= A \/ 8 <= L))) by (rewrite kHighMemBeg_val; clear -CEILB APL RA3; lia).
  set (P2 := fun x : acc => acc_ok (m_vm_lazy mo1) (aSc s) x).
  assert (PSTK2 : forall x n, lo <= x -> x + Z.of_nat n <= usp - 32 -> P2 (Z_to_bv 64 x, n)).
  { intros x n H1 H2. unfold P2. apply (pol_stack E0 FSB0 HR0 s mo1 Pq Dq AK1 WF ENV0); clear -CEILB H1 H2 LOC0 SPH; lia. }
  assert (PDAT2 : forall x n, 0xa4000 <= x -> x + Z.of_nat n <= 0x603000 -> P2 (Z_to_bv 64 x, n)).
  { intros x n H1 H2. unfold P2. apply (pol_img E0 FSB0 HR0 s mo1 Pq Dq AK1 WF ENV ENV0); clear -CEILB H1 H2; lia. }
  assert (PSH2 : forall x n, SH <= x -> x + Z.of_nat n <= SH + L / 8 -> P2 (Z_to_bv 64 x, n)).
  { intros x n H1 H2. unfold P2. apply (pol_sec_shadow E0 FSB0 HR0 s mo1 Pq Dq WF sc x n RESOK INSC); rewrite A_SB_val; unfold kShadowBase in H1, H2;
      clear -CEILB H1 H2 HA8 HL8; lia. }
  assert (PH2 : evtA asegs P2 (poison_post (Z_to_bv 64 0x35518) (Z_to_bv 64 (usp - 32)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 L)
                                           s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 lo SH (L / 8) 0)
                 (MS (mkR ra (Z_to_bv 64 (usp - 32)) gp tp (Z_to_bv 64 (cur - L)) t1' t2 (Z_to_bv 64 A) (Z_to_bv 64 A)
                          (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 0) a3' a4' a5' a6' a7' (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x35514) fc None m2 (seg_rom asegs))).
  { zstepA.
    eapply (poison_walk P2); rewrite ?USP2;
      [ exact SK2 | exact LOC0 | clear -CEILB LO; lia | clear -CEILB SPH LO LOC; lia | exact MI2 | exact (proj1 LDS2) | exact AM8 | exact LM8
      | clear -CEILB RA3; lia | exact AHI | exact ALC | exact APLp | clear; lia
      | right; unfold kClearShadowMmapThreshold; clear -CEILB CR AHI ALC HL8; lia
      | exact SHJ2 | exact PSTK2 | exact PDAT2 | exact PSH2 ]. }
  eapply (srzA_seg asegs (aSc s) (aNc s) (aEBc s) P2); [exact PH2| split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ TOK1)| intros x Hx; exact Hx] |].
  clear PH2. intros ms3 mo3 HQ3 AG3 [KIA3 _].
  destruct HQ3 as (t0' & t1'' & t2' & a0' & a1' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & SK3 & ZSH & PG3).
  rewrite USP2 in MU3, SK3.
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK1 AG3 KIA3) as TOK3.
  pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
  pose proof (AKern_frame _ _ _ _ Fvm3 Flz3 AK1) as AK3.
  replace (ret_pc (Z_to_bv 64 218392)) with (Z_to_bv 64 218392) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  replace (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in ZSH by reflexivity.
  assert (MU13 : munch [(usp - 624, usp); (0xaa7c0, 0xaa7c4); (0xaa590, 0xaa599); (0xaa5a8, 0xaa5b8); (0xaa7d8, 0xaa7e8);
                        (PA + 8 * Z.of_nat i, PA + 8 * Z.of_nat i + 8); (fst lastc + 24, fst lastc + 32); (SH, SH + L / 8)] m m3).
  { eapply munch_trans.
    - eapply munch_weaken; [| exact MU2]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia.
    - eapply munch_weaken; [| exact MU3]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia. }
  destruct (TRX m2 m3 WM3 MU3 FR2 MTX2 NRS2 SST2 GST2 ARR2 HDRC2 LST2 TC2 TST2 LDS2)
    as (FR3 & MTX3 & NRS3 & SST3 & GST3 & ARR3 & HDRC3 & LST3 & TC3 & TST3 & LDS3).
  assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM2| exact WM3]).
  (* [comment removed for export] *)
  pose proof (flush_hull A L AM8) as (FSB & FSE).
  pose proof (remap_range_flush A L AM8) as REQ.
  pose proof (rmp_pb_facts (flush_sb A) ltac:(rewrite FSB; unfold kShadowBase; clear -CEILB AHI HA8; lia)) as PBR.
  pose proof (rmp_pe_facts (flush_se A L) ltac:(rewrite FSE; unfold kShadowBase; clear -CEILB AHI HA8 RA3 HL8; lia)) as PER.
  set (PB := rmp_pb (flush_sb A)) in *. set (PE := rmp_pe (flush_se A L)) in *.
  rewrite FSB in PBR. rewrite FSE in PER.
  destruct (Z_lt_le_dec PB PE) as [HNE|HEMP].
  2:{ (* [comment removed for export] *)
    pose proof (ATOKu_intro E0 FSB0 HR0 L0 RES0 EB0 HR0_ok s a2 sc PERM Eres Ereg Eptr Enb Esb ltac:(clear -CEILB RA3; lia) R R' mo3 TOK3 AK3
                  ltac:(intros p _ [_ HI]; rewrite REQ in HI; cbn [fst snd] in HI; clear -CEILB HI HEMP; lia)) as TOKu3.
    assert (ENV2 : ENVOK E0 FSB0 (sA a2 s)) by (destruct TOKu3 as (_ & _ & E & _); exact E).
    destruct WF2 as (Pq2 & Dq2 & WFa2).
    assert (AK3b : AKern E0 a2 mo3) by (exact (AKern_sec_incl E0 a a2 mo3 AK3 INCL Ereg Eptr Enb Esb)).
    set (P3 := fun x : acc => acc_ok (m_vm_lazy mo3) (aSc (sA a2 s)) x).
    assert (PSTK3' : forall x n, lo <= x -> x + Z.of_nat n <= usp - 32 -> P3 (Z_to_bv 64 x, n)).
    { intros x n H1 H2. unfold P3. apply (pol_stack E0 FSB0 HR0 (sA a2 s) mo3 Pq2 Dq2 AK3b WFa2 ENV0); clear -CEILB H1 H2 LOC0 SPH; lia. }
    assert (PDAT3 : forall x n, 0xa4000 <= x -> x + Z.of_nat n <= 0x603000 -> P3 (Z_to_bv 64 x, n)).
    { intros x n H1 H2. unfold P3. apply (pol_img E0 FSB0 HR0 (sA a2 s) mo3 Pq2 Dq2 AK3b WFa2 ENV2 ENV0); clear -CEILB H1 H2; lia. }
    set (Qf := fun ms' : machine_state => exists (m3b : mem) (t0x a0x a1x a2x a3x a4x a5x a6x a7x : word),
          ms' = MS (mkR (Z_to_bv 64 0x35524) (Z_to_bv 64 (usp - 32)) gp tp t0x t1'' t2' (Z_to_bv 64 A) (Z_to_bv 64 A) a0x a1x a2x a3x a4x a5x a6x a7x
                        (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x35524) fc None m3b (seg_rom asegs)
          /\ mem_inv asegs m3b /\ stk asegs m3b lo (usp - 32) /\ wmono asegs m3 m3b /\ munch [(usp - 32 - 32, usp - 32)] m3 m3b).
    assert (PHf : evtA asegs P3 Qf (MS (mkR (Z_to_bv 64 0x35518) (Z_to_bv 64 (usp - 32)) gp tp t0' t1'' t2' (Z_to_bv 64 A) (Z_to_bv 64 A)
                                    a0' a1' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (Z_to_bv 64 0x35518) fc None m3 (seg_rom asegs))).
    { zstepA. zstepA. zstepA.   (* [comment removed for export] *)
      eapply flush_walk_none; rewrite ?USP2;
        [ exact PDAT3 | exact SK3 | exact LOC0 | clear -CEILB LO; lia | clear -CEILB LO LOC SPH; lia | exact MI3 | exact (proj1 (proj2 (proj2 (proj2 LDS3))))
        | clear -CEILB AHI; lia | clear -CEILB RA3; lia | clear -CEILB ALC; lia | clear -CEILB APL; lia | exact HEMP | exact PSTK3' | ].
      intros m3b a0x a1x a2x a3x a4x a5x a6x a7x t0x MI3b SK3b WM3b MU3b. ret_pc_lit.
      apply evtA_done. unfold Qf. exists m3b, t0x, a0x, a1x, a2x, a3x, a4x, a5x, a6x, a7x.
      split; [reflexivity|]. split; [exact MI3b|]. split; [exact SK3b|]. split; [exact WM3b| exact MU3b]. }
    eapply (srzA_seg asegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s) + L) P3 Qf);
      [exact PHf| split; [exact (ATOKu_KIA _ _ _ _ _ _ _ _ _ _ _ _ TOKu3)| intros x Hx; exact Hx] |].
    clear PHf. intros ms3b mo3b HQf AGf [KIAf _].
    destruct HQf as (m3b & t0x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & -> & MI3b & SK3b & WM3b & MU3b).
    pose proof (ATOKu_magree _ _ _ _ _ _ _ _ _ _ _ _ _ TOKu3 AGf KIAf) as TOKu3b.
    pose proof (magree_frame _ _ AGf) as (Ffdsf & Fvmf & Flzf & Ffsf & Fhf & Ftidf & _).
    pose proof (AKern_frame _ _ _ _ Fvmf Flzf AK3) as AK3f.
    assert (MU3b' : munch [(usp - 32 - 64, usp - 32); (SH, SH + L / 8)] m3 m3b).
    { eapply munch_weaken; [| exact MU3b]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy. lia. }
    destruct (TRX m3 m3b WM3b MU3b' FR3 MTX3 NRS3 SST3 GST3 ARR3 HDRC3 LST3 TC3 TST3 LDS3)
      as (FR3b & MTX3b & NRS3b & SST3b & GST3b & ARR3b & HDRC3b & LST3b & TC3b & TST3b & LDS3b).
    eapply (PH3b m3b mo3b);
      [ exact MI3b | exact SK3b | eapply wmono_trans; [exact WM13| exact WM3b]
      | eapply munch_trans; [exact MU13|]; eapply munch_weaken; [| exact MU3b]; intros y Hy; cbn in Hy |- *; clear -CEILB Hy; lia
      | exact FR3b | exact MTX3b | exact NRS3b | exact SST3b | exact GST3b | exact ARR3b | exact HDRC3b | exact LST3b | exact TC3b | exact TST3b | exact LDS3b
      | x23 ZSH MU3b WM3b; clear -CEILB LOC LO AHI ALC APL RA3 HL8; sdj; lia
      | exact TOKu3b | exact AK3f
      | rewrite Ffsf, Ffdsf, Ftidf, Ffs3, Ffds3, Ftid3, Ffs1, Ffds1, Ftid1; repeat split; reflexivity ]. }
  (* [comment removed for export] *)
  destruct PBR as (PB1 & PB2). destruct PER as (PE1 & PE2).
  assert (SHlo : 0x7fff8000 <= SH /\ SH + L / 8 <= 0x10007fff8000) by (unfold kShadowBase; clear -CEILB CR AHI ALC HA8 HL8 RA3; lia).
  destruct WF2 as (Pq2 & Dq2 & WFa2).
  set (P4 := fun x : acc => exists y n, x = (Z_to_bv 64 y, n) /\ ((lo <= y /\ y + Z.of_nat n <= usp) \/ (0xa4000 <= y /\ y + Z.of_nat n <= 0x603000))).
  assert (P4polA : forall moX, AKern E0 a moX -> forall x, P4 x -> acc_ok (m_vm_lazy moX) (aSc s) x).
  { intros moX AKX x (y & n & -> & [[H1 H2]|[H1 H2]]).
    - apply (pol_stack E0 FSB0 HR0 s moX Pq Dq AKX WF ENV0); clear -CEILB H1 H2 LOC0 SPH; lia.
    - apply (pol_img E0 FSB0 HR0 s moX Pq Dq AKX WF ENV ENV0); clear -CEILB H1 H2; lia. }
  assert (P4polB : forall moX, AKern E0 a2 moX -> ENVOK E0 FSB0 (sA a2 s) -> forall x, P4 x -> acc_ok (m_vm_lazy moX) (aSc (sA a2 s)) x).
  { intros moX AKX ENV2 x (y & n & -> & [[H1 H2]|[H1 H2]]).
    - apply (pol_stack E0 FSB0 HR0 (sA a2 s) moX Pq2 Dq2 AKX WFa2 ENV0); clear -CEILB H1 H2 LOC0 SPH; lia.
    - apply (pol_img E0 FSB0 HR0 (sA a2 s) moX Pq2 Dq2 AKX WFa2 ENV2 ENV0); clear -CEILB H1 H2; lia. }
  set (Qf := fun ms' : machine_state => exists (m3b : mem) (t0x a1x a2x a3x a4x a5x a6x a7x : word),
        ms' = MS (mkR (Z_to_bv 64 0x35524) (Z_to_bv 64 (usp - 32)) gp tp t0x t1'' t2' (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 0) a1x a2x a3x a4x a5x a6x a7x
                      (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x35524) fc None m3b (seg_rom asegs)
        /\ mem_inv asegs m3b /\ stk asegs m3b lo (usp - 32) /\ wmono asegs m3 m3b
        /\ munch [(usp - 32 - 32, usp - 32); (PB, PE)] m3 m3b
        /\ rw_cells asegs m3b PB [CB (Z.to_nat (PE - PB)) (repeat (Z_to_bv 8 0) (Z.to_nat (PE - PB)))]).
  eapply (rzA_madvise_al_cfg asegs (aSc s) (aNc s) (aEBc s) P4 Qf PB (PE - PB) _ mo3 K).
  - clear -CEILB PB1 SHlo. lia.
  - exact PB2.
  - clear -CEILB HNE. lia.
  - clear -CEILB PB2 PE2. Z.div_mod_to_equations. lia.
  - clear -CEILB PE1 SHlo. lia.
  - zstepA. zstepA. zstepA.   (* [comment removed for export] *)
    subst PB PE.
    eapply flush_walk_madv; rewrite ?USP2;
      [ intros y n H1 H2; exists y, n; split; [reflexivity| right; split; assumption]
      | exact SK3 | exact LOC0 | clear -CEILB LO; lia | clear -CEILB LO LOC SPH; lia | exact MI3 | exact (proj1 (proj2 (proj2 (proj2 LDS3))))
      | clear -CEILB AHI; lia | clear -CEILB RA3; lia | clear -CEILB ALC; lia | clear -CEILB APL; lia | exact HNE
      | intros y n H1 H2; exists y, n; split; [reflexivity| left; split; [exact H1| clear -CEILB H2; lia]] | ].
    intros m3b a1x a2x a3x a4x a5x a6x a7x t0x MI3b SK3b WM3b MU3b ZN. ret_pc_lit.
    apply evtA_done. unfold Qf. exists m3b, t0x, a1x, a2x, a3x, a4x, a5x, a6x, a7x.
    split; [reflexivity|]. split; [exact MI3b|]. split; [exact SK3b|]. split; [exact WM3b|]. split; [exact MU3b| exact ZN].
  - split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ TOK3)| exact (P4polA mo3 AK3)].
  - exact HK.
  - intros mo5 AG5 KIA5.
    pose proof (magree_frame _ _ AG5) as (Ffds5 & Fvm5 & Flz5 & Ffs5 & Fh5 & Ftid5 & _).
    destruct (ev_madvise E0 FSB0 HR0 L0 RES0 EB0 LS_L0 HS_L0 RES0_low R R' s mo3 mo5 sc PB (PE - PB) Pq Dq TOK3 AK3 WF INSC AG5 KIA5
                PB2 ltac:(clear -CEILB PB2 PE2; Z.div_mod_to_equations; lia) ltac:(clear -CEILB HNE; lia)
                ltac:(clear -CEILB PB1; lia) ltac:(clear -CEILB PE1; lia)) as (GATE & TOK6 & AK6).
    split; [exact GATE|].
    (* [comment removed for export] *)
    assert (MAT6 : forall p, In p (m_vm_materialized (m_madv mo5 PB (PE - PB))) -> ~ sc_interior sc (bv_unsigned p)).
    { intros p Hp [_ HI]. rewrite REQ in HI. cbn [fst snd] in HI.
      apply (m_madv_not_in mo5 PB (PE - PB) p ltac:(clear -CEILB PB1 SHlo RA3 HL8; lia) ltac:(clear -CEILB PB1 PE1 SHlo HNE RA3 HL8; lia)) in Hp. exact (Hp HI). }
    pose proof (ATOKu_intro E0 FSB0 HR0 L0 RES0 EB0 HR0_ok s a2 sc PERM Eres Ereg Eptr Enb Esb ltac:(clear -CEILB RA3; lia) R R' _ TOK6 AK6 MAT6) as TOKu6.
    assert (ENV2 : ENVOK E0 FSB0 (sA a2 s)) by (destruct TOKu6 as (_ & _ & EN & _); exact EN).
    assert (AK5b : AKern E0 a2 mo5).
    { apply (AKern_sec_incl E0 a a2 mo5); [exact (AKern_frame _ _ _ _ Fvm5 Flz5 AK3)| exact INCL| exact Ereg| exact Eptr| exact Enb| exact Esb]. }
    exists (aSc (sA a2 s)), (aNc (sA a2 s)), (aEBc (sA a2 s) + L).
    split; [exact (proj1 (ATOKu_KIA _ _ _ _ _ _ _ _ _ _ _ _ TOKu6))|]. split; [exact (P4polB mo5 AK5b ENV2)|].
    intros ms7 mo7 HQ7 AG7 KIA7 PS7.
    destruct HQ7 as (m3b & t0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & -> & MI3b & SK3b & WM3b & MU3b & ZN).
    pose proof (ATOKu_magree _ _ _ _ _ _ _ _ _ _ _ _ _ TOKu6 AG7 KIA7) as TOKu7.
    pose proof (magree_frame _ _ AG7) as (Ffds7 & Fvm7 & Flz7 & Ffs7 & Fh7 & Ftid7 & _).
    pose proof (AKern_frame _ _ _ _ Fvm7 Flz7 AK6) as AK7.
    assert (MU3b' : munch [(usp - 32 - 64, usp - 32); (SH, SH + L / 8)] m3 m3b).
    { eapply munch_weaken; [| exact MU3b]. intros y Hy. cbn in Hy |- *. clear -CEILB Hy PB1 PE1. lia. }
    destruct (TRX m3 m3b WM3b MU3b' FR3 MTX3 NRS3 SST3 GST3 ARR3 HDRC3 LST3 TC3 TST3 LDS3)
      as (FR3b & MTX3b & NRS3b & SST3b & GST3b & ARR3b & HDRC3b & LST3b & TC3b & TST3b & LDS3b).
    (* [comment removed for export] *)
    assert (ZSHb : rw_cells asegs m3b SH [CB (Z.to_nat (L / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (L / 8)))]).
    { pose proof (rw_cells_CB_zsub m3 SH _ (Z_to_bv 8 0) 0%nat (Z.to_nat (PB - SH)) ZSH ltac:(clear -CEILB PB1 PE1 HNE; lia)) as ZH.
      pose proof (rw_cells_CB_zsub m3 SH _ (Z_to_bv 8 0) (Z.to_nat (PE - SH)) (Z.to_nat (SH + L / 8 - PE)) ZSH ltac:(clear -CEILB PB1 PE1 HNE; lia)) as ZT.
      replace (SH + Z.of_nat 0) with SH in ZH by (clear; lia).
      replace (SH + Z.of_nat (Z.to_nat (PE - SH))) with PE in ZT by (clear -CEILB PB1 PE1 HNE; lia).
      replace (Z.to_nat (L / 8)) with (Z.to_nat (PB - SH) + Z.to_nat (PE - PB) + Z.to_nat (SH + L / 8 - PE))%nat by (clear -CEILB PB1 PE1 HNE; lia).
      rewrite !repeat_app, <- app_assoc.
      apply rw_cells_CB_merge3.
      - eapply rw_cells_transport; [exact ZH| exact MU3b| exact WM3b|]. clear -CEILB LOC LO PB1 PE1 HNE SHlo. sdj; lia.
      - replace (SH + Z.of_nat (Z.to_nat (PB - SH))) with PB by (clear -CEILB PB1; lia). exact ZN.
      - replace (SH + Z.of_nat (Z.to_nat (PB - SH)) + Z.of_nat (Z.to_nat (PE - PB))) with PE by (clear -CEILB PB1 PE1 HNE; lia).
        eapply rw_cells_transport; [exact ZT| exact MU3b| exact WM3b|]. clear -CEILB LOC LO PB1 PE1 HNE SHlo. sdj; lia. }
    pose proof (m_madv_frame mo5 PB (PE - PB)) as (Ufds & Ufs & _ & Utid & _).
    eapply (PH3b m3b mo7);
      [ exact MI3b | exact SK3b | eapply wmono_trans; [exact WM13| exact WM3b]
      | eapply munch_trans; [exact MU13|]; eapply munch_weaken; [| exact MU3b']; intros y Hy; cbn in Hy |- *; clear -CEILB Hy; lia
      | exact FR3b | exact MTX3b | exact NRS3b | exact SST3b | exact GST3b | exact ARR3b | exact HDRC3b | exact LST3b | exact TC3b | exact TST3b | exact LDS3b
      | exact ZSHb | exact TOKu7 | exact AK7
      | rewrite Ffs7, Ffds7, Ftid7, Ufs, Ufds, Utid, Ffs5, Ffds5, Ftid5, Ffs3, Ffds3, Ftid3, Ffs1, Ffds1, Ftid1; repeat split; reflexivity ].
Qed.
End LD.
End RC__1.
