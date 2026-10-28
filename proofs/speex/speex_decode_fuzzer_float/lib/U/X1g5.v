(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0px X0qc X0qp X0pv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1nt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_speex_bits_read_from : Z := 0x1c8cc.
Definition A_readfrom_join : Z := 0x1c904.
Definition A_readfrom_loop : Z := 0x1c914.
Definition A_readfrom_exit : Z := 0x1c960.
Definition A_fprintf : Z := 0x34aac.
Definition A_realloc : Z := 0x3326c.
Definition BITS_RSTDERR : Z := 0x3d110.
Definition BITS_GOT_STDERR : Z := 0x3c020.
Definition BITS_STDERR_VAR : Z := 0x3bfd0.
Definition BITS_FMT_notify : Z := 0x103f0.
Definition BITS_FMT_warning : Z := 0x106ae.
Definition A_MSG_PACKET_LARGER : Z := 0x10572.
Definition A_MSG_COULD_NOT_RESIZE : Z := 0x1067e.
Definition BITS_GLOBALS_TOP : Z := 0x6e000.
Definition BITS_FPRINTF_DEPTH : Z := 5632.
Definition BITS_REALLOC_STACK : Z := 8256.
Definition BITS_INT_MAX : Z := 2147483647.
Definition BITS_GOT_SSP : Z := 0x3c0d0.
Definition BITS_SSP_GUARD : Z := 0x6d6b8.

Definition READ_FROM_DEPTH : Z := 8320.

Definition READ_FROM_LEN_MAX : Z := 65536.

Definition bits_zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

Definition range_kept (m m' : mem) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2^64 -> lo <= a < hi ->
m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Section F.
Context {RCEIL : RunCeiling}.

Variables (notify warning : list Z -> X1qx.M PState unit).

Variable stderr_ok : mem -> Prop.
Variable sspc : mem -> word -> Prop.
Variable STR_TOP : Z.

Variable rhdr_known : PState -> bptr -> Prop.

Definition bits_cstr_arg (m : mem) (w : word) (s : list Z) (lo sp : Z) : Prop :=
exists slack : list byte,
bytes_at rsegs m (bv_unsigned w) (bits_zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned w + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s < BITS_INT_MAX - 256)
/\ (0 < bv_unsigned w)
/\ (bv_unsigned w + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned w)
/\ (BITS_GLOBALS_TOP <= bv_unsigned w \/ bv_unsigned w + zlength s + 1 + zlength slack <= STR_TOP).

Definition bits_fprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) (st : PState) : unit -> PState -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (BITS_RSTDERR, BITS_RSTDERR + 232)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ Fok10 F Ft
/\ stk rsegs m' lo (bv_unsigned sp)
/\ stderr_ok m'
/\ sspc m' canary
/\ st' = st.

Definition bits_fprintf_stmt (printer : list Z -> X1qx.M PState unit) (A_FMT : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (s : list Z) (lo : Z) (canary : word),
a0 = Z_to_bv 64 BITS_RSTDERR -> a1 = Z_to_bv 64 A_FMT -> bits_cstr_arg m a2 s lo (bv_unsigned sp) ->
stderr_ok m ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - BITS_FPRINTF_DEPTH) -> (BITS_GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) ->
sspc m canary -> mem_inv rsegs m -> frm0 fc ->
X1qx.implM rsegs (printer s) st
(bits_fprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_fprintf) fc None m (seg_rom rsegs)).
Definition bits_notify_stmt : Prop := bits_fprintf_stmt notify BITS_FMT_notify.
Definition bits_warning_stmt : Prop := bits_fprintf_stmt warning BITS_FMT_warning.

Definition bits_realloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (oldbytes : list byte) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m' /\ rw_cells rsegs m' A [CB (Z.to_nat old) oldbytes] /\ rhdr_known s' p
| Some q => exists A' junk,
a0 = Z_to_bv 64 A' /\ rblock_range A' n
/\ RHEAP s' ((q, A', n) :: lb_remove p LB) m'
/\ rw_cells rsegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n old)) oldbytes ++ junk)]
/\ rhdr_known s' q /\ (q = p -> A' = A)
end.

Definition bits_realloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbytes : list byte),
RHEAP s LB m -> In (p, A, old) LB -> rhdr_known s p -> X0qc.RBIG <= n ->
rw_cells rsegs m A [CB (Z.to_nat old) oldbytes] ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - BITS_REALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
implM rsegs (raw_realloc p n) s
(bits_realloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbytes m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_realloc) fc None m (seg_rom rsegs)).

Definition rheap_frame_stmt : Prop :=
forall s LB m m' W, RHEAP s LB m -> munch W m m' -> wmono rsegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Definition rheap_block_range_stmt : Prop :=
forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Definition rheap_blocks_nodup_stmt : Prop := forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Definition rheap_blocks_disjoint_stmt : Prop :=
forall s LB m b1 b2, RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.

Hypothesis HN : bits_notify_stmt.
Hypothesis HW : bits_warning_stmt.
Hypothesis HR : bits_realloc_stmt.
Hypothesis HFR : rheap_frame_stmt.
Hypothesis HBR : rheap_block_range_stmt.
Hypothesis HBD : rheap_blocks_disjoint_stmt.
Hypothesis STR_TOP_ok : 0x106b0 <= STR_TOP.
Hypothesis HBN : rheap_blocks_nodup_stmt.
Hypothesis stderr_ok_frame : forall m m', range_kept m m' BITS_RSTDERR (BITS_RSTDERR + 232) -> stderr_ok m -> stderr_ok m'.

Hypothesis HSSP : forall s LB m, RHEAP s LB m -> sspc m run_canary.

Definition read_from_X (A : Z) : list (Z * Z) := [(A, A + 48); (BITS_RSTDERR, BITS_RSTDERR + 232)].

Definition speex_bits_read_from_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(s : PState) (LB : list block) (b : bits_st bptr) (A lo B : Z) (m : mem)
(r : bits_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ frm0 fc' /\ Fok10 F Ft
/\ pres_except rsegs (rclient_addr (lb_remove (sb_chars b) LB) (bv_unsigned sp)) (read_from_X A) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ stderr_ok m'
/\ sb_owner r = 1 /\ rhdr_known s' (sb_chars r)
/\ exists D', RHEAP s' ((sb_chars r, D', sb_buf_size r) :: lb_remove (sb_chars b) LB) m'
/\ rblock_range D' (sb_buf_size r)
/\ bits_rep rsegs m' A D' r /\ bits_ok r.

#[using="Type"] Lemma firstn_S_nth {T} : forall (l : list T) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|].
rewrite (IH i d) by lia. reflexivity.
Qed.

#[using="Type"] Lemma upd_prefix_step : forall (pb ds : list byte) (i : nat),
(i < length pb)%nat -> (i < length ds)%nat ->
upd (firstn i pb ++ skipn i ds) i (nth i pb (Z_to_bv 8 0)) = firstn (S i) pb ++ skipn (S i) ds.
Proof.
intros pb ds i Hp Hd.
first [ pose proof (upd_app_split (firstn i pb ++ skipn i ds) i (nth i pb (Z_to_bv 8 0))
ltac:(rewrite length_app, length_firstn, length_skipn; lia)) as sfP_; sf_destruct 6%nat sfP_ as pre y post E Hlen Hupd | sf_fb; destruct (upd_app_split (firstn i pb ++ skipn i ds) i (nth i pb (Z_to_bv 8 0))
ltac:(rewrite length_app, length_firstn, length_skipn; lia)) as (pre & y & post & E & Hlen & Hupd) ].
rewrite Hupd.
assert (Epre : pre = firstn i pb).
{ apply (f_equal (firstn i)) in E. rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn in E.
replace (i - Nat.min i (length pb))%nat with 0%nat in E by lia. cbn in E. rewrite app_nil_r in E.
rewrite E, firstn_app, Hlen, Nat.sub_diag, firstn_all2 by lia. cbn. rewrite app_nil_r. reflexivity. }
assert (Epost : post = skipn (S i) ds).
{ apply (f_equal (skipn (S i))) in E. rewrite skipn_app, length_firstn in E.
replace (S i - Nat.min i (length pb))%nat with 1%nat in E by lia.
rewrite skipn_all2 in E by (rewrite length_firstn; lia). cbn [app] in E. rewrite skipn_skipn in E.
replace (1 + i)%nat with (S i) in E by lia. rewrite E.
rewrite skipn_app, Hlen. replace (S i - i)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
rewrite Epre, Epost. rewrite (firstn_S_nth pb i (Z_to_bv 8 0)) by lia. rewrite <- app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma range_kept_of_munch : forall W m m' lo hi,
munch W m m' -> wmono rsegs m m' -> (forall a, lo <= a < hi -> outside W a) -> range_kept m m' lo hi.
Proof.
intros W m m' lo hi MU WM OUT a Ha Hr. split; [|apply WM].
apply MU. rewrite wa_unsigned by lia. apply OUT. exact Hr.
Qed.

#[using="Type"] Lemma range_kept_of_rheap_pres : forall LB SP m m' lo hi,
rheap_pres LB SP m m' -> (forall a, lo <= a < hi -> rclient_addr LB SP a) -> range_kept m m' lo hi.
Proof. intros LB SP m m' lo hi HP HC a Ha Hr. apply HP; [exact Ha| apply HC; exact Hr]. Qed.

#[using="Type"] Lemma range_kept_of_pres_except : forall client X m m' lo hi,
pres_except rsegs client X m m' -> (forall a, lo <= a < hi -> client a /\ ~ in_ivs X a) -> range_kept m m' lo hi.
Proof. intros client X m m' lo hi HP HC a Ha Hr. destruct (HC a Hr) as [H1 H2]. apply HP; assumption. Qed.

#[using="Type"] Lemma range_kept_trans : forall m1 m2 m3 lo hi, range_kept m1 m2 lo hi -> range_kept m2 m3 lo hi -> range_kept m1 m3 lo hi.
Proof.
intros m1 m2 m3 lo hi H1 H2 a Ha Hr. destruct (H1 a Ha Hr) as [E1 W1]. destruct (H2 a Ha Hr) as [E2 W2].
split; [congruence| auto].
Qed.

#[using="Type"] Lemma outside_of_ranges : forall (client : Z -> Prop) (lo SP : Z) X W a,
Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ In iv X \/ (forall a', client a' -> ~ (fst iv <= a' < snd iv))) W ->
client a -> (SP <= a \/ a < lo) -> ~ in_ivs X a -> outside W a.
Proof.
intros client lo SP X W a FW Ca CASES Hx. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in FW. destruct FW as [F1 FW]. cbn. split; [|apply IH; exact FW].
cbn in F1. destruct F1 as [F1|[F1|F1]]; [lia| | exact (F1 a Ca)].
intros Hin. apply Hx. clear -Hin F1. induction X as [|iv X IH]; [destruct F1|].
cbn. destruct F1 as [E|F1]; [left; subst iv; cbn; lia| right; apply IH; exact F1].
Qed.

#[using="Type"] Lemma pres_except_of_munch_client : forall LB (SP lo : Z) X W m m',
(forall x, In x LB -> rblock_range (blk_addr x) (blk_size x)) -> alloc_ceiling <= lo -> lo <= SP ->
munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ In iv X \/ (forall a', rclient_addr LB SP a' -> ~ (fst iv <= a' < snd iv))) W ->
pres_except rsegs (rclient_addr LB SP) X m m'.
Proof.
intros LB SP lo X W m m' HBRc CEIL LO MU WM FW.
eapply pres_except_of_munch; [exact MU| exact WM|].
intros a Ha Hc Hx. unfold alloc_ceiling in CEIL.
eapply outside_of_ranges; [exact FW| exact Hc| | exact Hx].
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc.
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; lia|].
pose proof (HBRc _ Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ R4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & R4 & _) ]. unfold alloc_ceiling in R4. right. lia.
Qed.

#[using="HBD"] Lemma head_block_private : forall s1 (q : bptr) D' n LB1 SP lo m1 a',
RHEAP s1 ((q, D', n) :: LB1) m1 -> List.NoDup (map blk_id ((q, D', n) :: LB1)) -> rblock_range D' n ->
alloc_ceiling <= lo -> lo <= SP ->
rclient_addr LB1 SP a' -> ~ (D' <= a' < D' + n).
Proof.
intros s1 q D' n LB1 SP lo m1 a' HP1 ND BR CEIL LO Hc.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ]. unfold alloc_ceiling in BR4, CEIL.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc.
destruct Hc as [Hc|[Hc|(b2 & Hb2 & Hr2)]]; [lia| lia|].
assert (NE : blk_id (q, D', n) <> blk_id b2).
{ cbn [map] in ND. inversion ND as [|x l NI ND' E1]; subst. intros E. apply NI. rewrite E. apply in_map. exact Hb2. }
pose proof (HBD _ _ _ _ _ HP1 (or_introl eq_refl) (or_intror Hb2) NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. lia.
Qed.

#[using="Type"] Lemma pres_except_of_rheap_pres : forall LB SP SP' X m m',
rheap_pres LB SP' m m' -> SP' <= SP -> pres_except rsegs (rclient_addr LB SP) X m m'.
Proof.
intros LB SP SP' X m m' H HS a Ha Hc _. apply H; [exact Ha|].
unfold rclient_addr in *. destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
Qed.

#[using="Type"] Lemma lb_remove_cons : forall (p : bptr) x LB,
lb_remove p (x :: LB) = if bptr_eqb (blk_id x) p then lb_remove p LB else x :: lb_remove p LB.
Proof.
intros p x LB. unfold lb_remove. cbn. destruct (bptr_eqb (blk_id x) p); cbn; reflexivity.
Qed.

#[using="Type"] Lemma bptr_eqb_true : forall p q : bptr, bptr_eqb p q = true <-> p = q.
Proof.
intros [[r1 o1] z1] [[r2 o2] z2]. unfold bptr_eqb, aptr_eqb. cbn.
rewrite !andb_true_iff, N.eqb_eq, !Z.eqb_eq. split; [intros [[-> ->] ->]; reflexivity| intros E; inversion E; subst; auto].
Qed.

#[using="Type"] Lemma lb_remove_notin : forall (p : bptr) LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
intros p LB H. induction LB as [|x LB IH]; [reflexivity|].
cbn [map In] in H. rewrite lb_remove_cons. rewrite IH by tauto.
destruct (bptr_eqb (blk_id x) p) eqn:E; [|reflexivity].
exfalso. apply H. left. apply bptr_eqb_true. exact E.
Qed.

#[using="Type"] Lemma lb_remove_perm : forall LB (p : bptr) A n, List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
Permutation.Permutation LB ((p, A, n) :: lb_remove p LB).
Proof.
induction LB as [|x LB IH]; intros p A n ND HIN; [destruct HIN|].
cbn [map] in ND. inversion ND as [|y l NI ND' E]; subst.
rewrite lb_remove_cons. destruct HIN as [->|HIN].
- cbn [blk_id fst]. rewrite (proj2 (bptr_eqb_true p p) eq_refl).
rewrite lb_remove_notin by exact NI. apply Permutation.Permutation_refl.
- destruct (bptr_eqb (blk_id x) p) eqn:E.
+ exfalso. apply NI. apply bptr_eqb_true in E. rewrite E. change p with (blk_id (p, A, n)). apply in_map. exact HIN.
+ eapply Permutation.Permutation_trans; [apply Permutation.perm_skip; apply IH; [exact ND'| exact HIN]|].
apply Permutation.perm_swap.
Qed.

#[using="Type"] Lemma in_lb_remove : forall (p : bptr) LB x, In x (lb_remove p LB) -> In x LB /\ blk_id x <> p.
Proof.
intros p LB x. induction LB as [|y LB IH]; [intros H; destruct H|].
rewrite lb_remove_cons. destruct (bptr_eqb (blk_id y) p) eqn:E; intros H.
- destruct (IH H) as [H1 H2]. split; [right; exact H1| exact H2].
- destruct H as [<-|H].
+ split; [left; reflexivity|]. intros E2. apply (proj2 (bptr_eqb_true _ _)) in E2. congruence.
+ destruct (IH H) as [H1 H2]. split; [right; exact H1| exact H2].
Qed.

#[using="Type"] Lemma in_lb_remove_intro : forall (p : bptr) LB x, In x LB -> blk_id x <> p -> In x (lb_remove p LB).
Proof.
intros p LB x. induction LB as [|y LB IH]; [intros H; destruct H| intros H NE].
rewrite lb_remove_cons. destruct H as [E0|H].
- subst y. destruct (bptr_eqb (blk_id x) p) eqn:E; [exfalso; apply NE; apply bptr_eqb_true; exact E| left; reflexivity].
- destruct (bptr_eqb (blk_id y) p); [| right]; apply IH; assumption.
Qed.

#[using="Type"] Lemma nodup_ids_perm : forall LB LB', Permutation.Permutation LB LB' -> List.NoDup (map blk_id LB) -> List.NoDup (map blk_id LB').
Proof. intros LB LB' P ND. eapply Permutation.Permutation_NoDup; [apply Permutation.Permutation_map; exact P| exact ND]. Qed.

#[using="Type"] Lemma implM_retb : forall {X Y} (a : X) (f : X -> X1qx.M PState Y) (st : PState) Q ms,
implM rsegs (f a) st Q ms -> implM rsegs (X1qx.mbind (X1qx.mret a) f) st Q ms.
Proof. intros X Y a f st Q ms H. exact H. Qed.

#[using="Type"] Lemma impl_bind_cong_loc : forall {X Y} (t : itree node X) (k1 k2 : X -> itree node Y) (Q : Y -> machine_state -> Prop) ms,
(forall r ms', impl rsegs (at_node rsegs) (k1 r) Q ms' -> impl rsegs (at_node rsegs) (k2 r) Q ms') ->
impl rsegs (at_node rsegs) (X1bs.bind node t k1) Q ms -> impl rsegs (at_node rsegs) (X1bs.bind node t k2) Q ms.
Proof.
intros X Y t. induction t as [r|n k IH]; intros k1 k2 Q ms HK H; cbn [X1bs.bind] in *.
- apply HK. exact H.
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; [exact HK| apply Hk].
Qed.

#[using="Type"] Lemma impl_bind_assoc_loc : forall {X Y W} (t : itree node X) (g : X -> itree node Y) (f : Y -> itree node W) Q ms,
impl rsegs (at_node rsegs) (X1bs.bind node t (fun x => X1bs.bind node (g x) f)) Q ms ->
impl rsegs (at_node rsegs) (X1bs.bind node (X1bs.bind node t g) f) Q ms.
Proof.
intros X Y W t. induction t as [r|n k IH]; intros g f Q ms H; cbn [X1bs.bind] in *.
- exact H.
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. apply IH. apply Hk.
Qed.

#[using="Type"] Lemma implM_bind_assoc : forall {X Y W} (c : X1qx.M PState X) (g : X -> X1qx.M PState Y) (f : Y -> X1qx.M PState W) st Q ms,
implM rsegs (X1qx.mbind c (fun a => X1qx.mbind (g a) f)) st Q ms ->
implM rsegs (X1qx.mbind (X1qx.mbind c g) f) st Q ms.
Proof.
intros X Y W c g f st Q ms H. unfold implM, X1qx.mbind, ebind in *.
apply impl_bind_assoc_loc. eapply impl_bind_cong_loc; [| exact H].
intros [|[a s']] ms'; cbn [X1bs.bind fst snd]; intros H'; exact H'.
Qed.

#[using="Type"] Lemma map_unsigned_app_take : forall (n : Z) (pb ds0 : list byte) (d : list Z),
0 <= n -> d = map bv_unsigned (skipn (Z.to_nat n) ds0) ->
ztake n (map bv_unsigned pb) ++ d = map bv_unsigned (firstn (Z.to_nat n) pb ++ skipn (Z.to_nat n) ds0).
Proof. intros n pb ds0 d Hn ->. unfold ztake. rewrite map_app, firstn_map. reflexivity. Qed.

Definition SLACK_PACKET_LARGER : list byte := map (fun z => Z_to_bv 8 z) [78; 65; 78; 0; 68; 111; 32].
Definition SLACK_COULD_NOT_RESIZE : list byte := map (fun z => Z_to_bv 8 z) [119; 97].

#[using="Type"] Lemma ro_string_at : forall m (A0 : Z) (bs : list byte),
mem_inv rsegs m -> ro_bytes_b rsegs A0 bs = true -> 0 <= A0 -> A0 + Z.of_nat (length bs) <= 2^64 -> bytes_at rsegs m A0 bs.
Proof.
intros m A0 bs MI RB H0 HL.
pose proof (ro_cells_bytes_at rsegs m A0 _ (ro_cells_image rsegs m A0 bs MI RB H0 HL)) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.

#[using="STR_TOP_ok"] Lemma cstr_packet_larger : forall m lo spv, mem_inv rsegs m -> BITS_GLOBALS_TOP <= lo ->
bits_cstr_arg m (Z_to_bv 64 A_MSG_PACKET_LARGER) MSG_PACKET_LARGER lo spv.
Proof.
intros m lo spv MI GLO. unfold bits_cstr_arg, A_MSG_PACKET_LARGER, BITS_GLOBALS_TOP, BITS_INT_MAX in *.
exists SLACK_PACKET_LARGER. rewrite unsigned_lit64 by lia.
split; [apply ro_string_at; [exact MI| vm_compute; reflexivity| lia| cbn; lia]|].
split; [unfold MSG_PACKET_LARGER; cbn; repeat (constructor; [lia|]); constructor|].
unfold zlength, MSG_PACKET_LARGER, SLACK_PACKET_LARGER. cbn [length str_bytes map Z.of_nat]. cbn. lia.
Qed.

#[using="STR_TOP_ok"] Lemma cstr_could_not_resize : forall m lo spv, mem_inv rsegs m -> BITS_GLOBALS_TOP <= lo ->
bits_cstr_arg m (Z_to_bv 64 A_MSG_COULD_NOT_RESIZE) MSG_COULD_NOT_RESIZE lo spv.
Proof.
intros m lo spv MI GLO. unfold bits_cstr_arg, A_MSG_COULD_NOT_RESIZE, BITS_GLOBALS_TOP, BITS_INT_MAX in *.
exists SLACK_COULD_NOT_RESIZE. rewrite unsigned_lit64 by lia.
split; [apply ro_string_at; [exact MI| vm_compute; reflexivity| lia| cbn; lia]|].
split; [unfold MSG_COULD_NOT_RESIZE; cbn; repeat (constructor; [lia|]); constructor|].
unfold zlength, MSG_COULD_NOT_RESIZE, SLACK_COULD_NOT_RESIZE. cbn [length str_bytes map Z.of_nat]. cbn. lia.
Qed.

Section Body.
Variables (A P D len : Z) (pb : list byte) (b : bits_st bptr) (s : PState) (LB : list block) (lo B : Z).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem).
Hypothesis HP : RHEAP s LB m.
Hypothesis SPA : bv_unsigned sp <= A.
Hypothesis AB : A + 48 <= B.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - READ_FROM_DEPTH.

Local Notation POST := (speex_bits_read_from_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s LB b A lo B m).
Local Notation LBX p := (lb_remove p LB).

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac bdec := repeat match goal with
| |- context [?x <? ?y] => first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
| |- context [?x =? ?y] => first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia) | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
end; cbn [Z.b2z];
repeat match goal with |- context [Z.lxor ?x ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v end.

#[using="Type"] Lemma readfrom_loop : forall (k : nat) (i nchars D' : Z) (ds0 cur : list byte) (b1 : bits_st bptr) (rj : list byte)
(rav spv s3v a2v a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc1 : bv 32)
(W : list (Z * Z)) (m0 m1 : mem),
Z.of_nat k = nchars - i -> 0 <= i < nchars ->
nchars <= Z.of_nat (length ds0) -> nchars <= Z.of_nat (length pb) -> Z.of_nat (length ds0) < 2^24 ->
length rj = 16%nat -> rw_cells rsegs m1 A (bits_cells D' b1 rj) ->
cur = firstn (Z.to_nat i) pb ++ skipn (Z.to_nat i) ds0 -> length cur = length ds0 -> u8arr rsegs m1 D' cur ->
u8ro rsegs m1 P pb ->
(P + Z.of_nat (length pb) <= D' \/ D' + Z.of_nat (length ds0) <= P) ->
(A + 48 <= D' \/ D' + Z.of_nat (length ds0) <= A) ->
0 < D' -> 0 < A -> 0 < P -> a2v = Z_to_bv 64 (P + i) ->
munch ((D', D' + Z.of_nat (length ds0)) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m2 : mem),
ms' = MS (mkR rav spv gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 nchars) a1' a2' a3' a4' a5' a6' a7
(Z_to_bv 64 nchars) s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_exit) fc1 None m2 (seg_rom rsegs)
/\ rw_cells rsegs m2 A (bits_cells D' b1 rj)
/\ u8arr rsegs m2 D' (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0)
/\ u8ro rsegs m2 P pb
/\ munch ((D', D' + Z.of_nat (length ds0)) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2)
(MS (mkR rav spv gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 1) a2v a3 a4 a5 a6 a7
(Z_to_bv 64 nchars) s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_loop) fc1 None m1 (seg_rom rsegs)).
Proof.
clear HP SPA AB CEIL LO.
induction k as [|k IH]; intros i nchars D' ds0 cur b1 rj rav spv s3v a2v a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 Ft fc1 W m0 m1
Hk Hi Hnd Hnp Hds Lrj OBJ Ecur Lcur CUR SRC SEP1 SEP2 Dpos Apos Ppos HA2 MU WM MI; [lia|]. subst a2v.
unfold bits_cells in OBJ. unfold A_readfrom_loop.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ CUR) as DB. rewrite Lcur in DB.
pose proof (bytes_at_bound _ _ _ _ SRC) as PB.
assert (Hnth : nth_error pb (Z.to_nat i) = Some (nth (Z.to_nat i) pb (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read _ _ _ _ i _ _ SRC Hnth ltac:(lia) eq_refl) as RD.
zstep. ntk.
zstep. zstep. bdec.
zstep. ntk.
zstep. ntk.
zstep. zstep.
zstep. ntk.
zstep. zstep. zstep. bdec.
zstep. ntk.
zstep. ntk.
zstep. zstep. zstep.
pose proof (u8arr_store_ok rsegs _ _ _ i _ CUR ltac:(lia) eq_refl) as SOK.
zstep. rewrite le1_zxb.
pose proof (u8arr_write rsegs _ _ _ i (nth (Z.to_nat i) pb (Z_to_bv 8 0)) CUR ltac:(lia)) as CUR'.
clear CUR. store_done. try clear SOK.
zstep.
assert (Ecur' : upd cur (Z.to_nat i) (nth (Z.to_nat i) pb (Z_to_bv 8 0)) = firstn (Z.to_nat (i + 1)) pb ++ skipn (Z.to_nat (i + 1)) ds0).
{ rewrite Ecur. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply upd_prefix_step; lia. }
zstep. if_cases K; zify_cond K.
-
eapply (IH (i + 1) nchars D' ds0); try eassumption; try lia.
all: first [ rewrite upd_length; exact Lcur | f_equal; lia ].
-
replace nchars with (i + 1) by lia. rewrite <- Ecur'. unfold A_readfrom_exit.
apply evt_done. sf_eexists 7%nat. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); eassumption.
Qed.

#[using="HFR HBR HBD stderr_ok_frame HP SPA AB CEIL LO"] Lemma readfrom_tail : forall (nchars D' : Z) (ds0 : list byte) (b1 : bits_st bptr) (rj junk8 : list byte) (s' : PState)
(rav s3v a0v a1v a2v a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc1 : bv 32) (m1 : mem) (errv1 : word),
length rj = 16%nat -> rw_cells rsegs m1 A (bits_cells D' b1 rj) ->
u8arr rsegs m1 D' ds0 -> Z.of_nat (length ds0) = sb_buf_size b1 ->
u8ro rsegs m1 P pb ->
0 <= nchars <= sb_buf_size b1 -> nchars <= Z.of_nat (length pb) -> 1 <= sb_buf_size b1 < 2^24 ->
zdrop nchars (sb_data b1) = map bv_unsigned (skipn (Z.to_nat nchars) ds0) ->
sb_owner b1 = 1 -> 0 < D' -> 0 < P -> A mod 8 = 0 ->
(P + Z.of_nat (length pb) <= D' \/ D' + Z.of_nat (length ds0) <= P) ->
(P + Z.of_nat (length pb) <= A \/ A + 48 <= P) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 junk8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
mem_inv rsegs m1 -> rw_cells rsegs m1 (errno_addr tp) [C4 errv1] -> tp = Z_to_bv 64 RATP ->
rauxv_ok m1 B -> stderr_ok m1 ->
frm0 fc1 -> Fok10 F Ft ->
RHEAP s' ((sb_chars b1, D', sb_buf_size b1) :: LBX (sb_chars b)) m1 ->
List.NoDup (map blk_id ((sb_chars b1, D', sb_buf_size b1) :: LBX (sb_chars b))) ->
rblock_range D' (sb_buf_size b1) ->
pres_except rsegs (rclient_addr (LBX (sb_chars b)) (bv_unsigned sp)) (read_from_X A) m m1 ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> rhdr_known s' (sb_chars b1) ->
evt rsegs (POST (mkBits (sb_chars b1) (ztake nchars (map bv_unsigned pb) ++ zdrop nchars (sb_data b1)) (nchars * 8) 0 0
(sb_owner b1) 0 (sb_buf_size b1)) s')
(MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0v a1v a2v a3 a4 a5 a6 a7
(Z_to_bv 64 nchars) s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_join) fc1 None m1 (seg_rom rsegs)).
Proof.
intros until errv1. intros Lrj OBJ DST Lds SRC Hn Hnp Hbuf Hdrop OWN Dpos Ppos AL SEP1 SEP3 FR ST MI ERR TP AUX SE FRM HFt HP1 ND BR PX FA SO HK1.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold READ_FROM_DEPTH in LO.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ]. unfold alloc_ceiling in BR4.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. rewrite bits_cells_size in GB by exact Lrj.
pose proof (u8arr_bound _ _ _ _ DST) as DB. pose proof (bytes_at_bound _ _ _ _ SRC) as PB.
assert (ERRA : errno_addr tp = 316332) by (subst tp; rewrite unsigned_lit64 by (unfold RATP; lia); reflexivity).
rewrite ERRA in ERR.
assert (SEP2 : A + 48 <= D' \/ D' + Z.of_nat (length ds0) <= A) by lia.
pose proof (munch_refl [(D', D' + Z.of_nat (length ds0)); (A, A + 48)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
unfold A_readfrom_join.

eapply evt_cut with (P := fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word) (m2 : mem),
ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0' a1' a2' a3' a4' a5' a6' a7
(Z_to_bv 64 nchars) s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_exit) fc1 None m2 (seg_rom rsegs)
/\ rw_cells rsegs m2 A (bits_cells D' b1 rj)
/\ u8arr rsegs m2 D' (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0)
/\ munch [(D', D' + Z.of_nat (length ds0)); (A, A + 48)] m1 m2 /\ wmono rsegs m1 m2 /\ mem_inv rsegs m2).
{ zstep. if_cases K; zify_cond K.
-
replace (Z.to_nat nchars) with 0%nat by lia. cbn [firstn skipn app]. unfold A_readfrom_exit.
apply evt_done. sf_eexists 8%nat. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
- zstep. zstep. zstep. bdec.
eapply evt_mono.
+ eapply (readfrom_loop (Z.to_nat nchars) 0 nchars D' ds0 ds0 b1 rj); try eassumption; try lia; try reflexivity; f_equal; lia.
+ cbv beta. intros ms' sfH_; first [ sf_destruct 14%nat sfH_ as a1' a2' a3' a4' a5' a6' m2 -> OBJ2 DST2 _ MU2 WM2 MI2 | sf_fb; destruct sfH_ as (a1' & a2' & a3' & a4' & a5' & a6' & m2 & -> & OBJ2 & DST2 & _ & MU2 & WM2 & MI2) ].
sf_eexists 8%nat. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption. }
cbv beta. intros ms' sfH_; first [ sf_destruct 14%nat sfH_ as a0' a1' a2' a3' a4' a5' a6' m2 -> OBJ2 DST2 MU2 WM2 MI2 | sf_fb; destruct sfH_ as (a0' & a1' & a2' & a3' & a4' & a5' & a6' & m2 & -> & OBJ2 & DST2 & MU2 & WM2 & MI2) ].
clear MU WM. unfold A_readfrom_exit. unfold bits_cells in OBJ2.
pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn; lia)) as FR2.
pose proof (rw_cells_transport rsegs _ m1 m2 _ _ ERR MU2 WM2 ltac:(cbn; unfold RATP in *; lia)) as ERR2.
pose proof (stk_transport rsegs _ m1 m2 _ _ ST MU2 WM2 ltac:(cbn; lia)) as ST2.
clear FR ERR ST DST SRC OBJ MI.
remember (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0) as cur2 eqn:Ecur2.
assert (Lc2 : length cur2 = length ds0).
{ rewrite Ecur2, length_app, length_firstn, length_skipn. lia. }
zstep. rewrite wrap32_small, (Z.shiftr_div_pow2 _ 28), (Z.div_small _ (2^28)), swrap32_small by lia.
zstep. ntk.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
zstep. do 3 lstep.
do 6 zstep.
release_frame FR2 ST2 (bv_unsigned sp).
zstep.
assert (HPRIV : forall a', rclient_addr (LBX (sb_chars b)) (bv_unsigned sp) a' -> ~ (D' <= a' < D' + Z.of_nat (length ds0))).
{ intros a' Ha'. rewrite Lds. eapply (head_block_private s'); [exact HP1| exact ND| exact BR| exact CEIL| | exact Ha']. lia. }
unfold speex_bits_read_from_post. finish.
- rewrite ERRA. eassumption.
- eapply rauxv_ok_frame; [exact AUX| exact MU2| exact WM2|].
constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]].
- eapply pres_except_trans; [exact PX|].
eapply (pres_except_of_munch_client (LBX (sb_chars b)) (bv_unsigned sp) lo); [ | exact CEIL| lia| exact MU2| exact WM2|].
+ intros x Hx. apply in_lb_remove in Hx as [Hx _]. exact (HBR _ _ _ _ HP Hx).
+ constructor; [right; right; cbn [fst snd]; exact HPRIV|].
constructor; [right; left; left; reflexivity| constructor].
- eapply stderr_ok_frame; [|exact SE]. eapply range_kept_of_munch; [exact MU2| exact WM2|].
intros a Ha. unfold BITS_RSTDERR in Ha. cbn. lia.
- cbn [sb_chars sb_buf_size sb_owner]. exists D'. split; [|split; [exact BR| split]].
+ eapply HFR; [exact HP1| exact MU2| exact WM2|].
constructor; [right; right; eexists; split; [left; reflexivity| cbn; lia]|].
constructor; [left; cbn; lia| constructor].
+
split; [|split].
* exists rj. split; [exact Lrj|]. unfold bits_cells; cbn [sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size]. eassumption.
* exists cur2. split; [eassumption|]. rewrite Ecur2. apply map_unsigned_app_take; [lia| exact Hdrop].
* unfold bits_side; cbn. unfold BITS_BUF_MAX, BITS_SIZEOF. rewrite OWN. repeat split; try lia.
+ unfold bits_ok, bits_pos; cbn.
rewrite (map_unsigned_app_take nchars pb ds0 _ ltac:(lia) Hdrop), zlength_map_unsigned, <- Ecur2, Lc2.
repeat split; try lia.
Qed.

#[using="sspc STR_TOP HN HW HR HFR HBR HBD STR_TOP_ok HBN stderr_ok_frame HSSP HP SPA AB CEIL LO"] Lemma speex_bits_read_from_spec :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (errv : word) (pblk : block),

In (sb_chars b, D, sb_buf_size b) LB -> rhdr_known s (sb_chars b) ->
bits_rep rsegs m A D b -> bits_ok b -> sb_owner b = 1 -> X0qc.RBIG <= sb_buf_size b ->

u8ro rsegs m P pb -> 0 <= len <= Z.of_nat (length pb) -> len <= READ_FROM_LEN_MAX ->
In pblk (lb_remove (sb_chars b) LB) -> blk_addr pblk <= P -> P + Z.of_nat (length pb) <= blk_addr pblk + blk_size pblk ->

rauxv_ok m B -> bv_unsigned sp <= B -> stk rsegs m lo (bv_unsigned sp) -> bv_unsigned sp < 2^63 ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP -> frm0 fc ->
stderr_ok m ->
rw_cells rsegs m BITS_GOT_STDERR [C8 (Z_to_bv 64 BITS_STDERR_VAR)] ->
rw_cells rsegs m BITS_STDERR_VAR [C8 (Z_to_bv 64 BITS_RSTDERR)] ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 len ->
implM rsegs (speex_bits_read_from raw_realloc notify warning b (map bv_unsigned pb) len) s POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_read_from) fc None m (seg_rom rsegs)).
Proof.
intros until pblk. intros HIN HK REP OK OWN BIG SRC Hlen Hmax HPB PB1 PB2 AUX SPB ST SP63 ERR MI TP FRM SE GOT1 GOT2 -> -> ->.
pose proof (HBN _ _ _ HP) as HND.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as sfP_; first [ sf_destruct 13%nat sfP_ as In Ic Ib Io Iv Is Rc Rb Rp Rn Rs R1 Rov | sf_fb; destruct sfP_ as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov) ].
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos _ _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & _ & _ & SEP) ].
unfold bits_cells in OBJ. unfold int31, BITS_BUF_MAX, BITS_SIZEOF, READ_FROM_LEN_MAX in *.
unfold A_speex_bits_read_from, READ_FROM_DEPTH in *. unfold BITS_GOT_STDERR, BITS_STDERR_VAR, BITS_RSTDERR in GOT1, GOT2.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ DAT) as DB. pose proof (bytes_at_bound _ _ _ _ SRC) as PBB.
pose proof (in_lb_remove _ _ _ HPB) as [HPB' NEp].
pose proof (HBR _ _ _ _ HP HIN) as BRD. pose proof (HBR _ _ _ _ HP HPB') as BRP.
cbn [blk_addr blk_size fst snd] in BRD.
pose proof BRD as sfP_; first [ sf_destruct 5%nat sfP_ as BD1 BD2 BD3 BD4 BD5 | sf_fb; destruct sfP_ as (BD1 & BD2 & BD3 & BD4 & BD5) ]. pose proof BRP as sfP_; first [ sf_destruct 5%nat sfP_ as BP1 BP2 BP3 BP4 BP5 | sf_fb; destruct sfP_ as (BP1 & BP2 & BP3 & BP4 & BP5) ]. unfold alloc_ceiling in BD4, BP4.
assert (DJ : P + Z.of_nat (length pb) <= D \/ D + Z.of_nat (length bs) <= P).
{ pose proof (HBD _ _ _ _ _ HP HIN HPB' ltac:(cbn; congruence)) as DJ. cbn [blk_addr blk_size fst snd] in DJ. lia. }
assert (ERRA : errno_addr tp = 316332) by (subst tp; rewrite unsigned_lit64 by (unfold RATP; lia); reflexivity).
rewrite ERRA in ERR.
assert (PERM : Permutation.Permutation LB ((sb_chars b, D, sb_buf_size b) :: LBX (sb_chars b))).
{ apply lb_remove_perm; [exact HND| exact HIN]. }
pose proof (nodup_ids_perm _ _ PERM HND) as ND1.
unfold implM. iprefix.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 48%nat ST.
do 6 zstep.
zstep. ntk.
zstep. zstep. rewrite land7_mod8, AL.
zstep. ntk.
zstep. zstep.
zstep. rewrite sx32_small by (unfold int31; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
assert (HPL1 : RHEAP s LB m1).
{ eapply HFR; [exact HP| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
assert (HP1 : RHEAP s ((sb_chars b, D, sb_buf_size b) :: LBX (sb_chars b)) m1).
{ eapply RHEAP_perm; [exact HPL1| exact PERM]. }
assert (AUX1 : rauxv_ok m1 B).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL. lia. }
assert (SE1 : stderr_ok m1).
{ eapply stderr_ok_frame; [|exact SE]. eapply range_kept_of_munch; [exact MU| exact WM|]. intros a Ha. unfold BITS_RSTDERR in Ha. cbn. lia. }
assert (PX1 : pres_except rsegs (rclient_addr (LBX (sb_chars b)) (bv_unsigned sp)) (read_from_X A) m m1).
{ eapply (pres_except_of_munch_client (LBX (sb_chars b)) (bv_unsigned sp) lo); [ | exact CEIL| lia| exact MU| exact WM|].
+ intros x Hx. apply in_lb_remove in Hx as [Hx _]. exact (HBR _ _ _ _ HP Hx).
+ constructor; [left; cbn; lia| constructor]. }
zstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
-
zstep. zstep. zstep. do 5 zstep. zstep.
apply evt_done. unfold speex_bits_read_from.
replace (sb_buf_size b <? len) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite OWN. cbn [Z.eqb negb].
apply implM_bind_assoc.
eapply (implM_bind rsegs).
{ eapply HN with (lo := lo); try reflexivity; try exact SE1; try exact MI; try exact FRM.
all: rewrite ?unsigned_lit64 by lia.
- apply cstr_packet_larger; [assumption| unfold BITS_GLOBALS_TOP; lia].
- exact ST.
- unfold BITS_FPRINTF_DEPTH. lia.
- unfold BITS_GLOBALS_TOP. lia.
- lia.
- eapply HSSP. exact HP1. }
cbv beta. intros [] s2_ ms2 PN.
first [ sf_destruct 28%nat PN as x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 Ft fc2 m2 -> MUn WMn MI2 FRM2 HFt2 ST2 SE2 SSP2 -> | sf_fb; destruct PN as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & Ft & fc2 & m2 & -> & MUn & WMn & MI2 & FRM2 & HFt2 & ST2 & SE2 & SSP2 & ->) ].
rewrite !unsigned_lit64 in MUn, ST2 by lia.
replace (ret_pc (Z_to_bv 64 117180)) with (Z_to_bv 64 117180) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MUn WMn ltac:(cbn; unfold BITS_RSTDERR; lia)) as FR2.
pose proof (rw_cells_transport rsegs _ m1 m2 _ _ OBJ MUn WMn ltac:(cbn; unfold BITS_RSTDERR; lia)) as OBJ2.
pose proof (u8arr_transport rsegs _ m1 m2 _ _ DAT MUn WMn ltac:(cbn; unfold BITS_RSTDERR; lia)) as DAT2.
pose proof (u8ro_transport rsegs _ m1 m2 _ _ SRC MUn ltac:(cbn; unfold BITS_RSTDERR; lia)) as SRC2.
pose proof (rw_cells_transport rsegs _ m1 m2 _ _ ERR MUn WMn ltac:(cbn; unfold BITS_RSTDERR; lia)) as ERR2.
assert (AUX2 : rauxv_ok m2 B).
{ eapply rauxv_ok_frame; [exact AUX1| exact MUn| exact WMn|]. unfold BITS_RSTDERR.
constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]. }
assert (HPL2 : RHEAP s LB m2).
{ eapply HFR; [exact HPL1| exact MUn| exact WMn|]. unfold BITS_RSTDERR.
constructor; [left; cbn; lia|]. constructor; [|constructor].
right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. cbn. lia. }
assert (PX2 : pres_except rsegs (rclient_addr (LBX (sb_chars b)) (bv_unsigned sp)) (read_from_X A) m m2).
{ eapply pres_except_trans; [exact PX1|].
eapply (pres_except_of_munch_client (LBX (sb_chars b)) (bv_unsigned sp) lo); [ | exact CEIL| lia| exact MUn| exact WMn|].
+ intros x Hx. apply in_lb_remove in Hx as [Hx _]. exact (HBR _ _ _ _ HP Hx).
+ constructor; [left; cbn; lia|]. constructor; [right; left; right; left; reflexivity| constructor]. }
clear FR OBJ DAT SRC ERR GOT1 GOT2 AUX1 SE1 PX1 HP1 MU WM MI.

apply implM_bind_assoc. unfold implM. iprefix.
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit64 in K2 by lia; lia|]. clear K2.
zstep. zstep. zstep.
apply evt_done.
eapply (implM_bind rsegs).
{ eapply HR with (s := s) (LB := LB) (A := D) (old := sb_buf_size b) (lo := lo) (B := B) (oldbytes := bs);
try reflexivity; try exact HPL2; try exact HK; try exact AUX2; try exact MI2; try exact TP.
all: rewrite ?unsigned_lit64 by lia.
- exact HIN.
- unfold X0qc.RBIG in *. lia.
- replace (Z.to_nat (sb_buf_size b)) with (length bs) by lia. apply rw_cells_of_u8arr. exact DAT2.
- lia.
- exact ST2.
- exact CEIL.
- unfold BITS_REALLOC_STACK. lia.
- rewrite ERRA. exact ERR2.
- unfold MMAP_THRESHOLD. lia. }
cbv beta. intros r sR ms3 PR.
first [ sf_destruct 26%nat PR as x0' x1' x2' y0' y1' y2' y3' y4' y5' y6' y7' x3' x4' x5' x6' m3 errv3 -> MI3 ST3 ERR3 AUX3 PRES3 FA3 SO3 RES | sf_fb; destruct PR as (x0' & x1' & x2' & y0' & y1' & y2' & y3' & y4' & y5' & y6' & y7' & x3' & x4' & x5' & x6' & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PRES3 & FA3 & SO3 & RES) ].
rewrite !unsigned_lit64 in ST3, PRES3 by lia. rewrite ERRA in ERR3.
replace (ret_pc (Z_to_bv 64 117200)) with (Z_to_bv 64 117200) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -48) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [exact PRES3| exact FR2| left; cbn; lia]. }
assert (OBJ3 : rw_cells rsegs m3 A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sb_nbBits b)); C4 (Z_to_bv 64 (sb_charPtr b)); C4 (Z_to_bv 64 (sb_bitPtr b));
C4 (Z_to_bv 64 (sb_owner b)); C4 (Z_to_bv 64 (sb_overflow b)); C4 (Z_to_bv 64 (sb_buf_size b)); CB 16 rj]).
{ eapply rheap_pres_rw_cells; [exact PRES3| exact OBJ2| left; cbn; lia]. }
assert (SRC3 : u8ro rsegs m3 P pb).
{ eapply rheap_pres_bytes_at; [exact PRES3| exact SRC2|]. right; right. exists pblk. split; [exact HPB| lia]. }
assert (SE3 : stderr_ok m3).
{ eapply stderr_ok_frame; [|exact SE2]. eapply range_kept_of_rheap_pres; [exact PRES3|].
intros a Ha. unfold BITS_RSTDERR in Ha. right; left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
assert (PX3 : pres_except rsegs (rclient_addr (LBX (sb_chars b)) (bv_unsigned sp)) (read_from_X A) m m3).
{ eapply pres_except_trans; [exact PX2|]. eapply pres_except_of_rheap_pres; [exact PRES3| lia]. }
clear FR2 OBJ2 SRC2 ERR2 SE2 PX2 MI2 ST2 AUX2.
assert (SEP3 : P + Z.of_nat (length pb) <= A \/ A + 48 <= P) by lia.
destruct r as [q|].
+
first [ sf_destruct 8%nat RES as A' junkq -> BR' HP3 BLK HK3 _ | sf_fb; destruct RES as (A' & junkq & -> & BR' & HP3 & BLK & HK3 & _) ].
pose proof BR' as sfP_; first [ sf_destruct 5%nat sfP_ as BQ1 BQ2 BQ3 BQ4 BQ5 | sf_fb; destruct sfP_ as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5) ]. unfold alloc_ceiling in BQ4.
pose proof (rw_cells_bound _ _ _ _ BLK) as GB3. cbn [cells_size csize Nat.add length] in GB3.
pose proof (proj1 (proj1 BLK)) as LJ. cbn in LJ. destruct LJ as [LJ _].
pose proof (u8arr_of_rw_cells rsegs m3 A' _ _ BLK) as DST3. clear BLK.
remember (firstn (Z.to_nat (Z.min len (sb_buf_size b))) bs ++ junkq) as ds3 eqn:Eds3 in *.
assert (Lds3 : length ds3 = Z.to_nat len) by exact LJ.
assert (SEPq : P + Z.of_nat (length pb) <= A' \/ A' + len <= P).
{ pose proof (HBN _ _ _ HP3) as NDq. cbn [map] in NDq. inversion NDq as [|x l NI ND' E]; subst.
assert (NE : blk_id (q, A', len) <> blk_id pblk).
{ intros E. apply NI. cbn [blk_id fst] in E |- *. rewrite E. apply in_map. exact HPB. }
pose proof (HBD _ _ _ _ _ HP3 (or_introl eq_refl) (or_intror HPB) NE) as DJq. cbn [blk_addr blk_size fst snd] in DJq. (clear - DJq LJ Lds3 GB3 BQ5 BQ1 SEP3 A' junkq K DJ BP5 BP3 BP1 BD5 Lbs SEP Dpos Apos R1 bs PB2 PB1 Hlen pblk b pb len D P A RCEIL; lia). }
apply implM_retb. cbv beta iota. apply implM_ret.
pose proof (munch_refl [(A, A + 48)] m3) as MU3. pose proof (wmono_refl rsegs m3) as WM3.
zstep. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit64 in K3 by lia; lia|]. clear K3.
zstep. zstep. zstep.
rewrite OWN in OBJ3.
eapply (readfrom_tail len A' ds3
(mkBits q (sb_data b) (sb_nbBits b) (sb_charPtr b) (sb_bitPtr b) 1 (sb_overflow b) len) rj _ sR);
cbn [sb_chars sb_data sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size];
try eassumption; try reflexivity; try (clear - SEPq Lds3 LJ ds3 GB3 BQ5 BQ1 SEP3 A' K DJ BD5 Lbs SEP R1 bs Hlen b pb len D P A RCEIL BQ3 Hmax BP1 BD1 Dpos Apos PB1 pblk BP5 PB2; lia).
* unfold zdrop. rewrite Hbs. rewrite !skipn_all2; [reflexivity| rewrite Lds3; (clear - Lds3 LJ ds3 GB3 A' bs pb len RCEIL; lia)| rewrite length_map; (clear - SEPq Lds3 LJ ds3 GB3 BQ5 BQ1 SEP3 A' K DJ BD5 Lbs SEP Dpos R1 bs Hlen b pb len D P A RCEIL; lia)].
* rewrite ERRA. eassumption.
* eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
* eapply stderr_ok_frame; [|exact SE3]. eapply range_kept_of_munch; [exact MU3| exact WM3|].
intros a Ha. unfold BITS_RSTDERR in Ha. cbn. lia.
* eapply HFR; [exact HP3| exact MU3| exact WM3|]. constructor; [left; cbn; lia| constructor].
* exact (HBN _ _ _ HP3).
* eapply pres_except_trans; [exact PX3|].
eapply (pres_except_of_munch_client (LBX (sb_chars b)) (bv_unsigned sp) lo); [ | exact CEIL| lia| exact MU3| exact WM3|].
-- intros x Hx. apply in_lb_remove in Hx as [Hx _]. exact (HBR _ _ _ _ HP Hx).
-- constructor; [right; left; left; reflexivity| constructor].
+
first [ sf_destruct 4%nat RES as -> HP3 BLK HK3 | sf_fb; destruct RES as (-> & HP3 & BLK & HK3) ].
pose proof (u8arr_of_rw_cells rsegs m3 D _ _ BLK) as DAT3. clear BLK.
apply implM_bind_assoc. unfold implM. iprefix.
zstep. if_cases K3; zify_cond K3; [| exfalso; rewrite ?unsigned_lit64 in K3 by lia; lia]. clear K3.
zstep. rewrite sx32_small by (unfold int31; lia).
do 5 zstep. zstep.
apply evt_done.
eapply (implM_bind rsegs).
{ eapply HW with (lo := lo); try reflexivity; try exact SE3; try exact MI3; try exact FRM2.
all: rewrite ?unsigned_lit64 by lia.
- apply cstr_could_not_resize; [assumption| unfold BITS_GLOBALS_TOP; lia].
- exact ST3.
- unfold BITS_FPRINTF_DEPTH. lia.
- unfold BITS_GLOBALS_TOP. lia.
- lia.
- eapply HSSP. exact HP3. }
cbv beta. intros [] s4_ ms4 PW.
first [ sf_destruct 28%nat PW as x0'' x1'' x2'' y0'' y1'' y2'' y3'' y4'' y5'' y6'' y7'' x3'' x4'' x5'' x6'' Ft4 fc4 m4 -> MUw WMw MI4 FRM4 HFt4 ST4 SE4 SSP4 -> | sf_fb; destruct PW as (x0'' & x1'' & x2'' & y0'' & y1'' & y2'' & y3'' & y4'' & y5'' & y6'' & y7'' & x3'' & x4'' & x5'' & x6'' & Ft4 & fc4 & m4 & -> & MUw & WMw & MI4 & FRM4 & HFt4 & ST4 & SE4 & SSP4 & ->) ].
rewrite !unsigned_lit64 in MUw, ST4 by lia.
replace (ret_pc (Z_to_bv 64 117276)) with (Z_to_bv 64 117276) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FR3 MUw WMw ltac:(cbn; unfold BITS_RSTDERR; lia)) as FR4.
pose proof (rw_cells_transport rsegs _ m3 m4 _ _ OBJ3 MUw WMw ltac:(cbn; unfold BITS_RSTDERR; lia)) as OBJ4.
pose proof (u8arr_transport rsegs _ m3 m4 _ _ DAT3 MUw WMw ltac:(cbn; unfold BITS_RSTDERR; lia)) as DAT4.
pose proof (u8ro_transport rsegs _ m3 m4 _ _ SRC3 MUw ltac:(cbn; unfold BITS_RSTDERR; lia)) as SRC4.
pose proof (rw_cells_transport rsegs _ m3 m4 _ _ ERR3 MUw WMw ltac:(cbn; unfold BITS_RSTDERR; lia)) as ERR4.
assert (AUX4 : rauxv_ok m4 B).
{ eapply rauxv_ok_frame; [exact AUX3| exact MUw| exact WMw|]. unfold BITS_RSTDERR.
constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]. }
assert (HP4 : RHEAP sR LB m4).
{ eapply HFR; [exact HP3| exact MUw| exact WMw|]. unfold BITS_RSTDERR.
constructor; [left; cbn; lia|]. constructor; [|constructor].
right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. cbn. lia. }
assert (PX4 : pres_except rsegs (rclient_addr (LBX (sb_chars b)) (bv_unsigned sp)) (read_from_X A) m m4).
{ eapply pres_except_trans; [exact PX3|].
eapply (pres_except_of_munch_client (LBX (sb_chars b)) (bv_unsigned sp) lo); [ | exact CEIL| lia| exact MUw| exact WMw|].
+ intros x Hx. apply in_lb_remove in Hx as [Hx _]. exact (HBR _ _ _ _ HP Hx).
+ constructor; [left; cbn; lia|]. constructor; [right; left; right; left; reflexivity| constructor]. }
clear FR3 OBJ3 DAT3 SRC3 ERR3 AUX3 SE3 PX3 MI3 ST3.
apply implM_retb. cbv beta iota. apply implM_ret.
zstep.
eapply (readfrom_tail (sb_buf_size b) D bs b rj _ sR); try eassumption; try reflexivity; try (clear - R1 b SEP3 K DJ BP5 BP1 BD5 Lbs SEP Dpos Apos Rn In bs PB2 PB1 Hlen pblk pb len D P A RCEIL Rs BD1; lia).
* unfold zdrop. rewrite Hbs, skipn_map. reflexivity.
* rewrite ERRA. eassumption.
* eapply Fok10_trans; [exact HFt2| exact HFt4].
* eapply RHEAP_perm; [exact HP4| exact PERM].
-
apply evt_done. unfold speex_bits_read_from.
replace (sb_buf_size b <? len) with false by (symmetry; apply Z.ltb_ge; lia).
apply implM_retb. cbv beta iota. apply implM_ret.
eapply (readfrom_tail len D bs b rj _ s); try eassumption; try reflexivity; try lia.
all: try apply Fok10_refl.
+ unfold zdrop. rewrite Hbs, skipn_map. reflexivity.
+ rewrite ERRA. eassumption.
Qed.
End Body.

End F.
