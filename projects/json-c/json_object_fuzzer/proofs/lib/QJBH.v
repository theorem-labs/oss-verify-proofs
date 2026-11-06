(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy7F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy7F. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhzc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhzc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgPg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgPg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte) (only parsing).

Definition block : Type := (bptr * Z * Z)%type.
Definition blk_id (b : block) : bptr := fst (fst b).
Definition blk_slot (b : block) : cptr := fst (fst (fst b)).
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.

Definition lb_remove (p : bptr) (LB : list block) : list block :=
filter (fun b => negb (bptr_eqb (blk_id b) p)) LB.

Definition in_block (LB : list block) (a : Z) : Prop :=
exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
- rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
- exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
+ apply H. left. apply bptr_eqb_spec in E. exact E.
+ apply N. cbn [negb]. exact I.
Qed.

Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
unfold lb_remove. rewrite filter_cons, bptr_eqb_refl. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.

Record alayout : Type := mkAL {
al_malloc : Z;
al_free   : Z;
al_calloc : Z;
al_tp     : Z;
al_img_lo : Z;
al_img_hi : Z;
al_data_lo : Z;
al_data_hi : Z;
al_static : Z -> Prop;
al_malloc_stack : Z;
al_free_stack   : Z;
al_calloc_stack : Z
}.

Definition p_alloc_static (a : Z) : Prop :=
(0x292e8 <= a < 0x292f0)
\/ (0x3a634 <= a < 0x3a890 /\ ~ (0x3a760 <= a < 0x3a768))
\/ (0x3a770 <= a < 0x3aba8).

Definition p_alayout : alayout :=
mkAL 0x20c9c 0x20c98 0x20b60 0x3a6d8 0x10000 0x3b000 0x29000 0x3b000 p_alloc_static 8192 8192 8192.

Section WithLayout.
Context {BAND : Band}.
Variable segs : list Segment.
Variable AL : alayout.

Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> P a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma agree_on_write : forall (P : Z -> Prop) m a bs,
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(forall x, a <= x < a + Z.of_nat (length bs) -> ~ P x) ->
agree_on P m (write_to_mem m (wa a) bs).
Proof.
intros P m a bs Ha Hl HX x Hx HPx. split.
- rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
exfalso. apply (HX x); [lia| exact HPx].
- intros W. apply wview_write_mono. exact W.
Qed.

Lemma agree_on_of_munch : forall (P : Z -> Prop) W m m',
munch W m m' -> wmono segs m m' -> (forall x, P x -> 0 <= x < 2^64 -> outside W x) -> agree_on P m m'.
Proof.
intros P W m m' MU WM HX x Hx HPx. split.
- apply MU. rewrite wa_unsigned by lia. apply HX; assumption.
- apply WM.
Qed.

Lemma bytes_at_agree : forall P m m' A bs,
agree_on P m m' -> bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
bytes_at segs m' A bs.
Proof.
intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_agree : forall P m m' A n,
agree_on P m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at segs m' A n.
Proof.
intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree : forall P m m' A cs,
agree_on P m m' -> rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
rw_cells segs m' A cs.
Proof.
intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply wr_at_agree; eauto.
Qed.

Lemma ro_cells_agree : forall P m m' A cs,
agree_on P m m' -> ro_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
ro_cells segs m' A cs.
Proof.
intros P m m' A cs HP [Hwf HB] HR. split; [exact Hwf|].
eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
Qed.

Lemma u8arr_agree : forall P m m' A xs,
agree_on P m m' -> u8arr segs m A xs -> (forall a, A <= a < A + Z.of_nat (length xs) -> P a) ->
u8arr segs m' A xs.
Proof.
intros P m m' A xs HP [HB HW] HR. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto].
Qed.

Lemma u32arr_agree : forall P m m' A ws,
agree_on P m m' -> u32arr segs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) ->
u32arr segs m' A ws.
Proof.
intros P m m' A ws HP [HB HW] HR. split.
- eapply bytes_at_agree; eauto. rewrite u32s_length. intros; apply HR; lia.
- eapply wr_at_agree; eauto.
Qed.

Lemma u64arr_agree : forall P m m' A ws,
agree_on P m m' -> u64arr segs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) ->
u64arr segs m' A ws.
Proof.
intros P m m' A ws HP [HB HW] HR. split.
- eapply bytes_at_agree; eauto. rewrite u64s_length. intros; apply HR; lia.
- eapply wr_at_agree; eauto.
Qed.

Definition aclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
SP <= a \/ (al_data_lo AL <= a < al_data_hi AL /\ ~ al_static AL a) \/ in_block LB a.

Definition aheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
agree_on (aclient_addr LB SP) m m'.

Definition aclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (al_data_lo AL <= A /\ A + n <= al_data_hi AL /\ forall a, A <= a < A + n -> ~ al_static AL a)
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Definition ablock_range (A n : Z) : Prop :=
0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= band_lo /\ (A + n <= al_img_lo AL \/ al_img_hi AL <= A).

Definition aclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
band_lo <= fst iv
\/ (al_data_lo AL <= fst iv /\ snd iv <= al_data_hi AL /\ forall a, fst iv <= a < snd iv -> ~ al_static AL a)
\/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Definition aenv_write_ok (LB : list block) (B : Z) (iv : Z * Z) : Prop :=
(band_lo <= fst iv /\ snd iv <= B)
\/ (al_data_lo AL <= fst iv /\ snd iv <= al_data_hi AL /\ forall a, fst iv <= a < snd iv -> ~ al_static AL a)
\/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Definition aexposed (s : PState) (n : Z) : Prop :=
MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init (reservedZ segs)).

Section Stmts.
Variable HEAPp : PState -> list block -> mem -> Prop.
Variable AENV : Z -> mem -> Prop.

Definition amalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ AENV B m'
/\ aheap_pres LB (bv_unsigned sp) m m'
/\ ps_so s' = ps_so s /\ ps_x s' = ps_x s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ HEAPp s' LB m'
| Some p => exists A junk,
a0 = Z_to_bv 64 A /\ ablock_range A n
/\ HEAPp s' ((p, A, n) :: LB) m'
/\ rw_cells segs m' A [CB (Z.to_nat n) junk]
/\ (aexposed s n -> A = ptr_addr s' p)
end.

Definition amalloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z),
HEAPp s LB m -> AENV B m -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - al_malloc_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (al_tp AL) ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
implM segs (raw_malloc n) s
(amalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (al_malloc AL)) fc None m (seg_rom segs)).

Definition acalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ AENV B m'
/\ aheap_pres LB (bv_unsigned sp) m m'
/\ ps_so s' = ps_so s /\ ps_x s' = ps_x s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ HEAPp s' LB m'
| Some p => exists A,
a0 = Z_to_bv 64 A /\ ablock_range A n
/\ HEAPp s' ((p, A, n) :: LB) m'
/\ rw_cells segs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
end.

Definition acalloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (cnt sz lo B : Z),
HEAPp s LB m -> AENV B m -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - al_calloc_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (al_tp AL) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz < 2^32 ->
implM segs (if calloc_overflows cnt sz then mret None else raw_malloc (cnt * sz)) s
(acalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (al_calloc AL)) fc None m (seg_rom segs)).

Definition afree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (lo B : Z) (m : mem)
(r : unit) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ AENV B m'
/\ aheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ ps_so s' = ps_so s /\ ps_x s' = ps_x s
/\ HEAPp s' (lb_remove p LB) m'.

Definition afree_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z),
HEAPp s LB m -> In (p, A, n) LB -> AENV B m -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - al_free_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (al_tp AL) ->
a0 = Z_to_bv 64 A ->
implM segs (raw_free p) s
(afree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (al_free AL)) fc None m (seg_rom segs)).

Definition afree_null_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
a0 = Z_to_bv 64 0 ->
evt segs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (al_free AL)) fc None m (seg_rom segs)).
End Stmts.

Record alloc_iface : Type := mkAI {
ai_heap : PState -> list block -> mem -> Prop;
ai_env  : Z -> mem -> Prop;

ai_heap_ext : forall s s' LB m, ai_heap s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> ai_heap s' LB m;
ai_heap_perm : forall s LB LB' m, ai_heap s LB m -> Permutation LB LB' -> ai_heap s LB' m;
ai_heap_frame : forall s LB m m' W,
ai_heap s LB m -> munch W m m' -> wmono segs m m' -> Forall (aclient_write_ok LB) W -> ai_heap s LB m';
ai_env_frame : forall s LB B m m' W,
ai_heap s LB m -> ai_env B m -> munch W m m' -> wmono segs m m' -> Forall (aenv_write_ok LB B) W -> ai_env B m';
ai_block_range : forall s LB m b, ai_heap s LB m -> In b LB -> ablock_range (blk_addr b) (blk_size b);
ai_blocks_disjoint : forall s LB m b1 b2,
ai_heap s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1;
ai_blocks_nodup : forall s LB m, ai_heap s LB m -> List.NoDup (map blk_id LB);

ai_static_data : forall a, al_static AL a -> al_data_lo AL <= a < al_data_hi AL;

ai_malloc : amalloc_stmt ai_heap ai_env;
ai_calloc : acalloc_stmt ai_heap ai_env;
ai_free : afree_stmt ai_heap ai_env;
ai_free_null : afree_null_stmt
}.

End WithLayout.

Arguments aclient_addr AL LB SP a /.
Arguments aheap_pres segs AL LB SP m m' /.
Arguments agree_on segs P m m' /.

Definition PAI {BAND : Band} : Type := alloc_iface psegs p_alayout.
