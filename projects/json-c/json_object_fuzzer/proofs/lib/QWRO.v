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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte) (only parsing).

Definition ablock : Type := (aptr * Z * Z)%type.
Definition ablk_id (b : ablock) : aptr := fst (fst b).
Definition ablk_addr (b : ablock) : Z := snd (fst b).
Definition ablk_size (b : ablock) : Z := snd b.

Definition alb_remove (p : aptr) (LB : list ablock) : list ablock :=
filter (fun b => negb (aptr_eqb (ablk_id b) p)) LB.

Definition in_ablock (LB : list ablock) (a : Z) : Prop :=
exists b, In b LB /\ ablk_addr b <= a < ablk_addr b + ablk_size b.

Definition fframe : Type := (Z * Z)%type.
Definition ff_cls (f : fframe) : Z := fst f.
Definition ff_addr (f : fframe) : Z := snd f.
Definition ff_size (cls : Z) : Z := 64 * 2 ^ cls.
Definition in_fframe_body (FS : list fframe) (a : Z) : Prop :=
exists f, In f FS /\ ff_addr f <= a < ff_addr f + ff_size (ff_cls f) - 8.
Definition in_fframe_shadow (FS : list fframe) (a : Z) : Prop :=
exists f, In f FS /\ SH (ff_addr f) <= a < SH (ff_addr f) + ff_size (ff_cls f) / 8.
Definition ffs_remove (fa : Z) (FS : list fframe) : list fframe :=
filter (fun f => negb (ff_addr f =? fa)) FS.

Record alayoutA : Type := mkALA {
ala_malloc : Z;  ala_free : Z;  ala_calloc : Z;
ala_stack_malloc_0 : Z; ala_stack_malloc_9 : Z; ala_stack_free_9 : Z;
ala_asan_memset : Z; ala_set_shadow_00 : Z; ala_set_shadow_f8 : Z;
ala_tp : Z;
ala_gp : Z;
ala_img_lo : Z; ala_img_hi : Z;
ala_client_data : Z -> Prop;

ala_msites : list Z; ala_rsites : list Z;

ala_malloc_stack : Z; ala_free_stack : Z; ala_calloc_stack : Z;
ala_stack_malloc_stack : Z; ala_stack_free_stack : Z; ala_memset_stack : Z
}.

Definition a_client_data (a : Z) : Prop :=
(0x0ec920 <= a < 0x0ecd40)
\/ (0x0ecd40 <= a < 0x0eeb00)
\/ (0x0eeb08 <= a < 0x0eeb58)
\/ (0x184058 <= a < 0x184068)
\/ (0x614800 <= a < 0x624810)
\/ (0x624810 <= a < 0x624840)
\/ (0x624840 <= a < 0x625450)
\/ (0x625450 <= a < 0x62547c)
\/ (0x625480 <= a < 0x6254c8)
\/ (0x6254d0 <= a < 0x625518)
\/ (0x625558 <= a < 0x645560)
\/ (0x645568 <= a < 0x6457e0)
\/ (0x6457e8 <= a < 0x6458a0)
\/ (0x6458a0 <= a < 0x646940)
\/ (0x646db8 <= a < 0x646dbc)
\/ (0x7fffa000 <= a < 0x800c0e00)        .

Definition a_msites : list Z :=
[0x85ae0; 0x85b9c; 0x85bb0; 0x85cac; 0x85cf4; 0x85cfc; 0x8cf40; 0x8cf6c; 0x8cfa4; 0x91a24; 0x91a78; 0x91a9c;
0x91bcc; 0x91d04; 0x91d98; 0x91c94; 0x91e3c; 0x91ee8; 0x91fd4; 0x91ffc; 0x9217c; 0x92280; 0x92288; 0x932fc;
0x93310; 0x933d8; 0x933e0; 0x92cac; 0x935bc; 0x92f24; 0x92f3c; 0x93784; 0x938d0; 0x93d10; 0x94e48; 0x95f60;
0x98258; 0x9b424; 0x9b470; 0x9b4a8; 0x9b690; 0x9ba84; 0x9bd30; 0x9c05c; 0x9c0d0; 0x9c100; 0x9c11c; 0x9c124;
0x9c2e8; 0x9c358; 0x9c37c; 0x9c3b8; 0x9c3d4; 0x9c3dc; 0x9d38c; 0x9d474; 0x9d47c; 0x9d5b0; 0x9d770; 0x9d850;
0x9f3fc; 0x9f57c; 0x9f654; 0x9f6d0; 0x9f6d8; 0xa00d4; 0xa0770; 0xa0850; 0xa22a4; 0xa2308; 0xa2330; 0xa2478;
0xa2694; 0xa28b0; 0xa4170; 0xa41b8; 0xa4274; 0xa4380; 0xa43c8; 0xa4570; 0xa466c; 0xa4674; 0xa4c58].
Definition a_rsites : list Z := [0x9385c].
Definition a_alayout : alayoutA :=
mkALA 0x636a0 0x6369c 0x636a4 0x4a9bc 0x4ab30 0x4b9ec 0x61fb8 0x658c8 0x659e8
0x625520 0x10800 0x10000 0x647000 a_client_data a_msites a_rsites 4096 4096 4096 4096 4096 4096.

Definition depot_room (AL : alayoutA) : Prop :=
let r := Z.of_nat (length (ala_rsites AL)) in
5 * Z.of_nat (length (ala_msites AL)) * (1 + r + r * r + r * r * r) + 8 <= 65000.

Record aentry : Type := mkAE {
ae_sp0 : Z;
ae_stack_top : Z;
ae_fs_base : Z;
ae_L : ALay
}.
Definition ae_stack_bottom (RE : aentry) : Z := ae_stack_top RE - 0x800000.

Notation ablock_rangeA_lia A n := ((appr_lia A n /\ 32769 - 32769 * zhigh A <= n) /\ A mod 16 = 0 /\ 0 <= n
/\ A + n <= band_lo /\ A + 4096 <= band_lo) (only parsing).
Notation fframe_rangeA_lia RE cls f := (ae_fs_base RE + 0x9000 <= f /\ f + ff_size cls <= ae_fs_base RE + 0xb00000 /\ f mod 64 = 0
/\ appr_lia f (ff_size cls) /\ f + ff_size cls <= band_lo) (only parsing).

Section WithLayout.
Context {BAND : Band}.
Variable segs : list Segment.
Variable atn : node -> machine_state -> Prop.
Variable AL : alayoutA.

Local Notation implMA := (@implMG PStateA segs atn).

Definition aclient_addrA (LB : list ablock) (FS : list fframe) (SP : Z) (a : Z) : Prop :=
SP <= a
\/ ala_client_data AL a
\/ in_ablock LB a
\/ in_fframe_body FS a
\/ in_fframe_shadow FS a
\/ (SH band_lo <= a < SH (2^47))
\/ (SH (ala_img_lo AL) <= a < SH 0x0e4000).

Definition aheap_presA (LB : list ablock) (FS : list fframe) (SP : Z) (m m' : mem) : Prop :=
agree_on segs (aclient_addrA LB FS SP) m m'.

Lemma aheap_presA_trans : forall LB FS SP m1 m2 m3,
aheap_presA LB FS SP m1 m2 -> aheap_presA LB FS SP m2 m3 -> aheap_presA LB FS SP m1 m3.
Proof. intros LB FS SP m1 m2 m3. apply agree_on_trans. Qed.
Lemma aheap_presA_weaken : forall LB LB' FS FS' SP SP' m m',
aheap_presA LB FS SP m m' -> SP <= SP' ->
(forall b, In b LB' -> In b LB) -> (forall f, In f FS' -> In f FS) ->
aheap_presA LB' FS' SP' m m'.
Proof.
intros LB LB' FS FS' SP SP' m m' H HS HL HF. eapply agree_on_mono; [exact H|].
intros a [Hc|[Hc|[(b & Hb & Hr)|[(f & Hf & Hr)|[(f & Hf & Hr)|[Hc|Hc]]]]]];
unfold aclient_addrA.
- left; lia.
- right; left; exact Hc.
- right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
- right; right; right; left. exists f. split; [apply HF; exact Hf| exact Hr].
- right; right; right; right; left. exists f. split; [apply HF; exact Hf| exact Hr].
- do 5 right; left; exact Hc.
- do 6 right; exact Hc.
Qed.

Definition aclient_rangeA (LB : list ablock) (FS : list fframe) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (forall a, A <= a < A + n -> ala_client_data AL a)
\/ (exists b, In b LB /\ ablk_addr b <= A /\ A + n <= ablk_addr b + ablk_size b)
\/ (exists f, In f FS /\ ff_addr f <= A /\ A + n <= ff_addr f + ff_size (ff_cls f) - 8)
\/ (exists f, In f FS /\ SH (ff_addr f) <= A /\ A + n <= SH (ff_addr f) + ff_size (ff_cls f) / 8)
\/ (SH band_lo <= A /\ A + n <= SH (2^47))
\/ (SH (ala_img_lo AL) <= A /\ A + n <= SH 0x0e4000).

Lemma aclient_rangeA_addr : forall LB FS SP A n a,
aclient_rangeA LB FS SP A n -> A <= a < A + n -> aclient_addrA LB FS SP a.
Proof.
intros LB FS SP A n a HR Ha. unfold aclient_rangeA, aclient_addrA in *.
destruct HR as [H|[H|[(b & Hb & H1 & H2)|[(f & Hf & H1 & H2)|[(f & Hf & H1 & H2)|[[H1 H2]|[H1 H2]]]]]]].
- left; lia.
- right; left; apply H; lia.
- right; right; left; exists b; split; [exact Hb|lia].
- right; right; right; left; exists f; split; [exact Hf|lia].
- right; right; right; right; left; exists f; split; [exact Hf|lia].
- do 5 right; left; lia.
- do 6 right; lia.
Qed.

Lemma aheap_presA_bytes_at : forall LB FS SP m m' A bs,
aheap_presA LB FS SP m m' -> bytes_at segs m A bs -> aclient_rangeA LB FS SP A (Z.of_nat (length bs)) ->
bytes_at segs m' A bs.
Proof. intros. eapply bytes_at_agree; eauto. intros; eapply aclient_rangeA_addr; eauto. Qed.

Lemma aheap_presA_rw_cells : forall LB FS SP m m' A cs,
aheap_presA LB FS SP m m' -> rw_cells segs m A cs -> aclient_rangeA LB FS SP A (Z.of_nat (cells_size cs)) ->
rw_cells segs m' A cs.
Proof. intros. eapply rw_cells_agree; eauto. intros; eapply aclient_rangeA_addr; eauto. Qed.

Definition ablock_rangeA (A n : Z) : Prop :=
(appr A n /\ (n <= 32768 -> KHI <= A)) /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= band_lo /\ A + 4096 <= band_lo.

Definition fframe_rangeA (RE : aentry) (cls f : Z) : Prop :=
ae_fs_base RE + 0x9000 <= f /\ f + ff_size cls <= ae_fs_base RE + 0xb00000 /\ f mod 64 = 0 /\ appr f (ff_size cls)
/\ f + ff_size cls <= band_lo.

Definition aclient_write_okA (LB : list ablock) (FS : list fframe) (iv : Z * Z) : Prop :=
band_lo <= fst iv
\/ (forall a, fst iv <= a < snd iv -> ala_client_data AL a)
\/ (exists b, In b LB /\ ablk_addr b <= fst iv /\ snd iv <= ablk_addr b + ablk_size b)
\/ (exists f, In f FS /\ ff_addr f <= fst iv /\ snd iv <= ff_addr f + ff_size (ff_cls f) - 8)
\/ (exists f, In f FS /\ SH (ff_addr f) <= fst iv /\ snd iv <= SH (ff_addr f) + ff_size (ff_cls f) / 8)
\/ (SH band_lo <= fst iv /\ snd iv <= SH (2^47)).

Definition unw_valid (RE : aentry) (v : Z) : Prop :=
ae_stack_bottom RE < v /\ v < ae_stack_top RE - 16 /\ v mod 8 = 0.

Definition unw_readable (RE : aentry) (m : mem) (lo : Z) : Prop :=
forall x, lo <= x < ae_stack_top RE -> 0 <= x < 2^64 -> exists b, mrd segs m (wa x) = Some b.
Definition DP_N : Z := 0x5d4098.
Definition DEPOT_CAP : Z := 32000.
Definition depot_n (m : mem) (n : Z) : Prop := rw_cells segs m DP_N [C4 (Z_to_bv 64 n)] /\ 1 <= n.

Definition depot_keep (m m' : mem) : Prop := forall n, depot_n m n -> depot_n m' n.

Lemma depot_keep_of_munch : forall W m m', munch W m m' -> wmono segs m m' -> Forall (fun iv => snd iv <= DP_N \/ DP_N + 4 <= fst iv) W -> depot_keep m m'.
Proof.
intros W m m' MU WM HW n [RC P]. split; [| exact P]. eapply rw_cells_transport; [exact RC| exact MU| exact WM|].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - HW. induction HW as [|[lo hi] W' H1 HW IH]; cbn [disjoint_from fst snd] in *; [exact I|]. split; [lia| exact IH].
Qed.

Definition errno_keep (m m' : mem) : Prop := agree_on segs (fun a => 0x62547c <= a < 0x62547c + 4) m m'.

Lemma errno_keep_trans : forall m1 m2 m3, errno_keep m1 m2 -> errno_keep m2 m3 -> errno_keep m1 m3.
Proof. intros m1 m2 m3 H1 H2. eapply agree_on_trans; eassumption. Qed.
Lemma errno_keep_of_munch : forall W m m', munch W m m' -> wmono segs m m' -> Forall (fun iv => snd iv <= 0x62547c \/ 0x62547c + 4 <= fst iv) W -> errno_keep m m'.
Proof.
intros W m m' MU WM HW. eapply agree_on_of_munch; [exact MU| exact WM|]. intros y Hy _. clear - HW Hy.
induction HW as [|[lo hi] W' H1 HW IH]; cbn [outside fst snd] in *; [exact I|]. split; [lia| exact IH].
Qed.

Definition free_keep (m m' : mem) : Prop := depot_keep m m' /\ errno_keep m m'.

Definition amemset_whereA (LB : list ablock) (FS : list fframe) (dst n : Z) : Prop :=
(exists p A n0, In (p, A, n0) LB /\ A <= dst /\ dst + n <= A + n0)
\/ (exists c f, In (c, f) FS /\ f <= dst /\ dst + n <= f + ff_size c).

Section Stmts.
Variable RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop.

Definition std_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB : list ablock) (FS : list fframe) (lo : Z) (m : mem) (s' : PStateA) (ms' : machine_state)
(K : word  -> mem -> Prop) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ aheap_presA LB FS (bv_unsigned sp) m m'
/\ ps_soa s' = ps_soa s /\ ps_xa s' = ps_xa s
/\ K a0 m'.

Definition amallocA_stmt (L : ALay) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (n lo dn : Z),
ae_L RE = L ->
RUN s LB FS RE m ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_malloc_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (ala_tp AL) -> gp = Z_to_bv 64 (ala_gp AL) ->
unw_readable RE m (bv_unsigned sp) -> depot_n m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 n -> 0 <= n <= 2^26 ->
implMA (raw_malloc_A L n) s
(fun r s' ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ RUN s' LB FS RE m'
| Some p => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req p = n
/\ RUN s' ((p, A, n) :: LB) FS RE m'
/\ rw_cells segs m' A [CB (Z.to_nat n) junk]
/\ blk_shadow segs m' A n
/\ (forall mb k, p = ASec mb k -> A = mb + kSecUserOff)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_malloc AL)) fc None m (seg_rom segs)).

Definition acallocA_stmt (L : ALay) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (cnt sz lo dn : Z),
ae_L RE = L ->
RUN s LB FS RE m ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_calloc_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (ala_tp AL) -> gp = Z_to_bv 64 (ala_gp AL) ->
unw_readable RE m (bv_unsigned sp) -> depot_n m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 2^26 ->
implMA (if calloc_overflows cnt sz then mret None else raw_malloc_A L (cnt * sz)) s
(fun r s' ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ RUN s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (cnt * sz) /\ aptr_req p = cnt * sz
/\ RUN s' ((p, A, cnt * sz) :: LB) FS RE m'
/\ rw_cells segs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
/\ blk_shadow segs m' A (cnt * sz)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_calloc AL)) fc None m (seg_rom segs)).

Definition afreeA_stmt (L : ALay) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A n lo dn : Z),
ae_L RE = L ->
RUN s LB FS RE m -> In (p, A, n) LB ->
qroom (ps_a s) p ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_free_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (ala_tp AL) -> gp = Z_to_bv 64 (ala_gp AL) ->
unw_readable RE m (bv_unsigned sp) -> depot_n m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A ->
implMA (raw_free_A L p) s
(fun _ s' ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun _ m' => (exists dn', depot_n m' dn' /\ dn <= dn' <= dn + 1) /\ errno_keep m m' /\ RUN s' (alb_remove p LB) FS RE m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_free AL)) fc None m (seg_rom segs)).

Definition afree_nullA_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (lo : Z),
RUN s LB FS RE m ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_free_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (ala_tp AL) -> gp = Z_to_bv 64 (ala_gp AL) ->
unw_readable RE m (bv_unsigned sp) ->
a0 = Z_to_bv 64 0 ->
evt segs (fun ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s ms'
(fun _ m' => depot_keep m m' /\ errno_keep m m' /\ RUN s LB FS RE m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_free AL)) fc None m (seg_rom segs)).

Definition fframe_cap (cls : Z) : Z := 2 ^ (14 - cls).

Definition astack_mallocA_stmt (cls entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (size lo : Z),
RUN s LB FS RE m ->
Z.of_nat (length (filter (fun f => ff_cls f =? cls) FS)) < fframe_cap cls ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_stack_malloc_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (ala_tp AL) -> gp = Z_to_bv 64 (ala_gp AL) ->
a0 = Z_to_bv 64 size -> 0 < size <= ff_size cls -> size mod 8 = 0 ->
evt segs (fun ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s ms'
(fun a0' m' => depot_keep m m' /\ exists f junk,
a0' = Z_to_bv 64 f /\ fframe_rangeA RE cls f
/\ RUN s LB ((cls, f) :: FS) RE m'
/\ rw_cells segs m' f [CB (Z.to_nat (ff_size cls - 8)) junk]
/\ rw_cells segs m' (SH f) [CB (Z.to_nat (ff_size cls / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ff_size cls / 8)))]))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition astack_free9A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (f size lo : Z),
RUN s LB FS RE m -> In (9, f) FS ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_stack_free_stack AL ->
mem_inv segs m ->
tp = Z_to_bv 64 (ala_tp AL) -> gp = Z_to_bv 64 (ala_gp AL) ->
a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 size -> 0 < size <= ff_size 9 -> size mod 8 = 0 ->
evt segs (fun ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (ffs_remove f FS) lo m s ms'
(fun _ m' => RUN s LB (ffs_remove f FS) RE m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_stack_free_9 AL)) fc None m (seg_rom segs)).

Definition aasan_memsetA_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (dst c n lo : Z) (old : list byte)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry),
RUN s LB FS RE m ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_memset_stack AL ->
mem_inv segs m ->
a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 -> 0 < n ->
rw_cells segs m dst [CB (Z.to_nat n) old] ->
shadow_base segs m ->

(forall k, 0 <= k -> dst / 8 * 8 + 8 * k < dst + n ->
exists v, bytes_at segs m (SH (dst / 8 * 8) + k) [Z_to_bv 8 v] /\
(v = 0 \/ (0 < v < 8 /\ dst + n <= dst / 8 * 8 + 8 * k + v))) ->
appr dst n -> dst + n <= band_lo ->
64 < n <= 2 ^ 43 \/ amemset_whereA LB FS dst n ->

evt segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(dst, dst + n); (lo, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' dst [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ala_asan_memset AL)) fc None m (seg_rom segs)).

Definition aset_shadowA_stmt (entry v : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (dst n lo : Z) (old : list byte)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry),
RUN s LB FS RE m ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ala_memset_stack AL ->
mem_inv segs m ->
a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 n -> 0 < n < 2^32 ->
rw_cells segs m dst [CB (Z.to_nat n) old] ->
evt segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(dst, dst + n); (lo, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' dst [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).
End Stmts.

Local Notation wz := (Z_to_bv 64).

Definition asan_global_cells (beg size size_rz name loc : Z) : list cell :=
[C8 (wz beg); C8 (wz size); C8 (wz size_rz); C8 (wz name); C8 (wz loc); C8 (wz 0); C8 (wz 0); C8 (wz 0xffffffffffffffff)].
Definition asan_globals_cells : list cell :=
asan_global_cells 0x23100 2 32 0x201dd 0x23280
++ asan_global_cells 0x23120 9 32 0x12744 0x23280
++ asan_global_cells 0x23140 9 32 0x20b7c 0x23280
++ asan_global_cells 0x23160 5 32 0x10ba8 0x23280
++ asan_global_cells 0x23180 4 32 0x19e6a 0x23280
++ asan_global_cells 0x231a0 2 32 0x2231c 0x23280
++ asan_global_cells 0x231c0 2 32 0x14f62 0x23280
++ asan_global_cells 0x231e0 2 32 0x13d6f 0x23280
++ asan_global_cells 0x23200 2 32 0x1e78b 0x23280
++ asan_global_cells 0x23220 2 32 0x19735 0x23280
++ asan_global_cells 0x23240 5 32 0x1973c 0x23280
++ asan_global_cells 0x23260 6 32 0x18193 0x23280
++ asan_global_cells 0x23380 23 64 0x201dd 0x239e0
++ asan_global_cells 0x233c0 5 32 0x2231c 0x239e0
++ asan_global_cells 0x233e0 18 64 0x14f62 0x239e0
++ asan_global_cells 0x23420 58 96 0x19735 0x239e0
++ asan_global_cells 0x23480 2 32 0x115df 0x239e0
++ asan_global_cells 0x234a0 2 32 0x1717a 0x239e0
++ asan_global_cells 0x234c0 2 32 0x21518 0x239e0
++ asan_global_cells 0x234e0 2 32 0x115e6 0x239e0
++ asan_global_cells 0x23500 8 32 0x1b15e 0x239e0
++ asan_global_cells 0x23520 2 32 0x21520 0x239e0
++ asan_global_cells 0x23540 5 32 0x1f6fa 0x239e0
++ asan_global_cells 0x23560 3 32 0x1d678 0x239e0
++ asan_global_cells 0x23580 2 32 0x1a939 0x239e0
++ asan_global_cells 0x235a0 8 32 0x1cdb8 0x239e0
++ asan_global_cells 0x235c0 3 32 0x11e2d 0x239e0
++ asan_global_cells 0x235e0 2 32 0x11e35 0x239e0
++ asan_global_cells 0x23600 3 32 0x18c03 0x239e0
++ asan_global_cells 0x23620 3 32 0x1b166 0x239e0
++ asan_global_cells 0x23640 3 32 0x14f69 0x239e0
++ asan_global_cells 0x23660 3 32 0x14442 0x239e0
++ asan_global_cells 0x23680 3 32 0x13d76 0x239e0
++ asan_global_cells 0x236a0 3 32 0x17a32 0x239e0
++ asan_global_cells 0x236c0 3 32 0x10bc5 0x239e0
++ asan_global_cells 0x236e0 3 32 0x18c0b 0x239e0
++ asan_global_cells 0x23700 9 32 0x181a2 0x239e0
++ asan_global_cells 0x23720 5 32 0x10bcd 0x239e0
++ asan_global_cells 0x23740 6 32 0x13d7e 0x239e0
++ asan_global_cells 0x23760 4 32 0x115ee 0x239e0
++ asan_global_cells 0x23780 4 32 0x12751 0x239e0
++ asan_global_cells 0x237a0 9 32 0x18c13 0x239e0
++ asan_global_cells 0x237c0 10 32 0x1cdc0 0x239e0
++ asan_global_cells 0x237e0 6 32 0x1a941 0x239e0
++ asan_global_cells 0x23800 4 32 0x18c1b 0x239e0
++ asan_global_cells 0x23820 3 32 0x115f6 0x239e0
++ asan_global_cells 0x23840 8 32 0x1580a 0x239e0
++ asan_global_cells 0x23860 2 32 0x1b16e 0x239e0
++ asan_global_cells 0x23880 3 32 0x22323 0x239e0
++ asan_global_cells 0x238a0 2 32 0x14f71 0x239e0
++ asan_global_cells 0x238c0 49 96 0x115fe 0x239e0
++ asan_global_cells 0x23920 78 128 0x16998 0x239e0
++ asan_global_cells 0x239a0 30 64 0x1e792 0x239e0
++ asan_global_cells 0x23ae0 27 64 0x1d680 0x23bc0
++ asan_global_cells 0x23b20 21 64 0x201dd 0x23bc0
++ asan_global_cells 0x23b60 24 64 0x2231c 0x23bc0
++ asan_global_cells 0x23ba0 13 32 0x14f62 0x23bc0
++ asan_global_cells 0x23c00 24 64 0x1d680 0x240c0
++ asan_global_cells 0x23c40 11 32 0x201dd 0x240c0
++ asan_global_cells 0x23c60 12 32 0x2231c 0x240c0
++ asan_global_cells 0x23c80 13 32 0x14f62 0x240c0
++ asan_global_cells 0x23ca0 12 32 0x13d6f 0x240c0
++ asan_global_cells 0x23cc0 12 32 0x1e78b 0x240c0
++ asan_global_cells 0x23ce0 10 32 0x19735 0x240c0
++ asan_global_cells 0x23d00 12 32 0x1b898 0x240c0
++ asan_global_cells 0x23d20 12 32 0x115df 0x240c0
++ asan_global_cells 0x23d40 14 32 0x1717a 0x240c0
++ asan_global_cells 0x23d60 12 32 0x21518 0x240c0
++ asan_global_cells 0x23d80 13 32 0x115e6 0x240c0
++ asan_global_cells 0x23da0 14 32 0x1b15e 0x240c0
++ asan_global_cells 0x23dc0 13 32 0x21520 0x240c0
++ asan_global_cells 0x23de0 13 32 0x1f6fa 0x240c0
++ asan_global_cells 0x23e00 13 32 0x1d678 0x240c0
++ asan_global_cells 0x23e20 14 32 0x1a939 0x240c0
++ asan_global_cells 0x23e40 12 32 0x1cdb8 0x240c0
++ asan_global_cells 0x23e60 13 32 0x11e2d 0x240c0
++ asan_global_cells 0x23e80 12 32 0x11e35 0x240c0
++ asan_global_cells 0x23ea0 13 32 0x18c03 0x240c0
++ asan_global_cells 0x23ec0 14 32 0x1b166 0x240c0
++ asan_global_cells 0x23ee0 13 32 0x14f69 0x240c0
++ asan_global_cells 0x23f00 13 32 0x14442 0x240c0
++ asan_global_cells 0x23f20 13 32 0x13d76 0x240c0
++ asan_global_cells 0x23f40 13 32 0x17a32 0x240c0
++ asan_global_cells 0x23f60 13 32 0x10bc5 0x240c0
++ asan_global_cells 0x23f80 14 32 0x18c0b 0x240c0
++ asan_global_cells 0x23fa0 12 32 0x181a2 0x240c0
++ asan_global_cells 0x23fc0 13 32 0x10bcd 0x240c0
++ asan_global_cells 0x23fe0 13 32 0x13d7e 0x240c0
++ asan_global_cells 0x24000 12 32 0x115ee 0x240c0
++ asan_global_cells 0x24020 13 32 0x12751 0x240c0
++ asan_global_cells 0x24040 12 32 0x1444a 0x240c0
++ asan_global_cells 0x24060 11 32 0x1f702 0x240c0
++ asan_global_cells 0x24080 13 32 0x18c13 0x240c0
++ asan_global_cells 0x240a0 13 32 0x1cdc0 0x240c0
++ asan_global_cells 0x24140 60 96 0x1d680 0x24260
++ asan_global_cells 0x241a0 43 96 0x201dd 0x24260
++ asan_global_cells 0x24200 64 96 0x2231c 0x24260
++ asan_global_cells 0xe4ec0 56 96 0x1b874 0x239e0
++ asan_global_cells 0xec920 3 32 0x1b85e 0x23280
++ [C8 (wz 0xec940); C8 (wz 0x8); C8 (wz 0x20); C8 (wz 0x10bb6); C8 (wz 0x239e0); C8 (wz 0x0); C8 (wz 0x0); C8 (wz 0x624860)]
++ asan_global_cells 0xec960 8 32 0x1e79a 0x23ab0
++ asan_global_cells 0xec980 4 32 0x12759 0x23ab0
++ asan_global_cells 0xec9a0 128 160 0x20b90 0x240c0
++ asan_global_cells 0xeca40 576 704 0x18c23 0x240c0
++ asan_global_cells 0x624840 8 32 0x14420 0x239e0
++ asan_global_cells 0x624880 4 32 0x201e4 0x240c0
++ asan_global_cells 0x6248a0 256 320 0x12772 0x240f7.

Definition rt_consts_at (m : mem) : Prop :=

ro_cells segs m 0x0e4ab8 [C8 (wz 0x9b3cc); C8 (wz 0x3e10c)]

/\ ro_cells segs m 0x0e80b0 [C8 (wz 0x0ecd40)]
/\ ro_cells segs m 0x0e8188 [C8 (wz 0xcec58); C8 (wz 0)]
/\ ro_cells segs m 0x0e8e20 [C8 (wz 0x0e80b0); C8 (wz 0)]
/\ ro_cells segs m 0x0e8ec0 [C8 (wz 0x0ed040); C8 (wz 0x0eeb00)]
/\ ro_cells segs m 0x0e8f90 [C8 (wz 0x645560)]
/\ ro_cells segs m 0x0e8fc0 [C8 (wz 0x0e4ac8); C8 (wz 0x0e4ab8)]

/\ ro_cells segs m 0x645560 [C8 band_guard]

/\ ro_cells segs m 0x6457e0 [C8 (wz 0x1000)]
/\ ro_cells segs m (0x183ce8 + 219) [C1 (Z_to_bv 8 1)]
/\ ro_cells segs m (0x183ce8 + 244) [C1 (Z_to_bv 8 1)]

/\ ro_cells segs m 0x0e8198 [C8 (wz 0x181c60)]
/\ ro_cells segs m 0x0e81a8 [C8 (wz 0x183ce8); C8 (wz 0x0ef9b8)]
/\ ro_cells segs m 0x0e81c0 [C8 (wz 0x0f2ea8); C8 (wz 0x0f2eb0); C8 (wz 0x0f2ea0); C8 (wz 0x0ea1d0)]
/\ ro_cells segs m 0x0e81f0 [C8 (wz 0x0ea218)]
/\ ro_cells segs m 0x0e8d28 [C8 (wz 0x0f2e99)]

/\ ro_cells segs m 0x0ea178 [C8 (wz 0xde3d4)]
/\ ro_cells segs m 0x0ea1c8 [C8 (wz 0xdda10); C8 (wz 0xdde14)]
/\ ro_cells segs m 0x0ea218 [C8 (wz 0x220a0)]
/\ ro_cells segs m 0x0ea068 [C8 (wz 0xdd914)]
/\ ro_cells segs m 0x0ea078 [C8 (wz 0xe3934)]
/\ ro_cells segs m 0x0ea080 [C8 (wz 0xd5bc4)]
/\ ro_cells segs m 0x0ea098 [C8 (wz 0xdb6ac); C8 (wz 0xd5f20)]

/\ ro_cells segs m 0x0f2e98 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
/\ ro_cells segs m 0x0f2ea0 [C8 (wz 0x7fffffffffff); C8 (wz 0); C8 (wz 0)]
/\ ro_cells segs m 0x0f1a1c [C1 (Z_to_bv 8 1)]
/\ ro_cells segs m 0x181c60 [C8 (wz 0x1000)]
/\ ro_cells segs m 0x183d3c [C1 (Z_to_bv 8 1)]
/\ ro_cells segs m 0x183de3 [C1 (Z_to_bv 8 1)]
/\ ro_cells segs m 0x0ef9d0 [C4 (wz 1)]
/\ ro_cells segs m 0x0efab0 [C4 (wz 0)]
/\ ro_cells segs m 0x0efa78 [C8 (wz 0); C8 (wz 0); C8 (wz 0)]

/\ rw_cells segs m 0x0eeb00 [C8 (wz 1)]
/\ rw_cells segs m 0x0efa70 [C8 (wz 0)]

/\ ro_cells segs m 0x0ea020 [C8 (wz 0x0ea020)]

/\ ro_cells segs m 0x183d60 [C8 (wz 0xffffffffffffffff)]

/\ ro_cells segs m 0x0ef9d5 [C1 (Z_to_bv 8 1)] /\ ro_cells segs m 0x0e81e0 [C8 (wz 0x0ea1c8)]
/\ ro_cells segs m 0x0e81a0 [C8 (wz 0x0ea208)] /\ ro_cells segs m 0x0e8ea8 [C8 (wz 0x0a4110)] /\ ro_cells segs m 0x0ea028 [C8 (wz 0x0de074)]
/\ ro_cells segs m 0x0ea0a8 [C8 (wz 0x0db6c8)] /\ ro_cells segs m 0x0ea150 [C8 (wz 0x0cf4a0)] /\ ro_cells segs m 0x0ea1a0 [C8 (wz 0x0dceac)]
/\ ro_cells segs m 0x183ddd [C1 (Z_to_bv 8 0)] /\ ro_cells segs m 0x183de2 [C1 (Z_to_bv 8 1)]

/\ ro_cells segs m 0x0e8e58 [C8 (wz 0x09f854)] /\ ro_cells segs m 0x0e8e88 [C8 (wz 0x093a24)]

/\ ro_cells segs m 0x183de5 [C1 (Z_to_bv 8 1)] /\ ro_cells segs m 0x0ea050 [C8 (wz 0x0ddf20)] /\ ro_cells segs m 0x0e8e38 [C8 (wz 0x09dd50)]
/\ ro_cells segs m 0x0e8e40 [C8 (wz 0x09e4a0)] /\ ro_cells segs m 0x0e8e48 [C8 (wz 0x09e8d8)] /\ ro_cells segs m 0x0e8e68 [C8 (wz 0x09f8e4)]
/\ ro_cells segs m 0x0e8e98 [C8 (wz 0x0a6060)] /\ ro_cells segs m 0x0e8ea0 [C8 (wz 0x0a62ec)] /\ ro_cells segs m 0x0e8eb0 [C8 (wz 0x0a53f4)]
/\ ro_cells segs m 0x0e8e60 [C8 (wz 0x09f85c)] /\ ro_cells segs m 0x0e8e70 [C8 (wz 0x0a0a78)] /\ ro_cells segs m 0x0e8e78 [C8 (wz 0x0ec940)]

/\ ro_cells segs m 0x0e8050 [C8 (wz 0x01499c)] /\ ro_cells segs m 0x0e4ec8 [C8 (wz 0x09c508)] /\ ro_cells segs m 0x0e4ed0 [C8 (wz 0x09c600)] /\ ro_cells segs m 0x0e4ed8 [C8 (wz 0x09c60c)]
/\ ro_cells segs m 0x0e4ee0 [C8 (wz 0x09c878)] /\ ro_cells segs m 0x0e4ee8 [C8 (wz 0x09cd50)] /\ ro_cells segs m 0x0e4ef0 [C8 (wz 0x09d200)]

/\ ro_cells segs m 0x0e8e50 [C8 (wz 0x09edbc)]

/\ ro_cells segs m 0x0e8e80 [C8 (wz 0x093680)].

Definition ai_rt_consts_stmt (RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop) : Prop :=
forall s LB FS RE m, RUN s LB FS RE m -> rt_consts_at m.

Definition ai_errno_stmt (RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop) : Prop :=
forall s LB FS RE m, RUN s LB FS RE m -> exists v : word, rw_cells segs m 0x62547c [C4 v].
Definition ai_errno_frame_stmt (RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop) : Prop :=
forall s LB FS RE m m' (v : word), RUN s LB FS RE m -> munch [(0x62547c, 0x62547c + 4)] m m' -> wmono segs m m' ->
rw_cells segs m' 0x62547c [C4 v] -> RUN s LB FS RE m'.

Definition ai_nbhd_stmt (RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop) : Prop :=
forall s LB FS RE m p n, RUN s LB FS RE m -> amemset_whereA LB FS p n -> 0 < n ->
(exists w : word, rw_cells segs m (8 * (SH p / 8)) [C8 w])
/\ (exists w : word, rw_cells segs m (8 * (SH (p + n - 1) / 8)) [C8 w]).

Record alloc_ifaceA : Type := mkAAI {
ai_run : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop;

ai_run_ext : forall s s' LB FS RE m, ai_run s LB FS RE m -> ps_a s' = ps_a s -> ai_run s' LB FS RE m;
ai_run_perm : forall s LB LB' FS FS' RE m, ai_run s LB FS RE m -> Permutation LB LB' -> Permutation FS FS' ->
ai_run s LB' FS' RE m;
ai_run_frame : forall s LB FS RE m m' W,
ai_run s LB FS RE m -> munch W m m' -> wmono segs m m' -> Forall (aclient_write_okA LB FS) W ->
ai_run s LB FS RE m';
ai_block_range : forall s LB FS RE m b, ai_run s LB FS RE m -> In b LB -> ablock_rangeA (ablk_addr b) (ablk_size b);
ai_block_small : forall s LB FS RE m b, ai_run s LB FS RE m -> In b LB -> ablk_size b <= 2^26;
ai_blocks_disjoint : forall s LB FS RE m b1 b2,
ai_run s LB FS RE m -> In b1 LB -> In b2 LB -> ablk_id b1 <> ablk_id b2 ->
ablk_addr b1 + Z.max (ablk_size b1) 1 <= ablk_addr b2 \/ ablk_addr b2 + Z.max (ablk_size b2) 1 <= ablk_addr b1;
ai_blocks_nodup : forall s LB FS RE m, ai_run s LB FS RE m -> List.NoDup (map ablk_id LB);
ai_block_shadow : forall s LB FS RE m p A n, ai_run s LB FS RE m -> In (p, A, n) LB -> blk_shadow segs m A n;
ai_fframe_range : forall s LB FS RE m f, ai_run s LB FS RE m -> In f FS -> fframe_rangeA RE (ff_cls f) (ff_addr f);
ai_fframes_disjoint : forall s LB FS RE m f1 f2,
ai_run s LB FS RE m -> In f1 FS -> In f2 FS -> ff_addr f1 <> ff_addr f2 ->
ff_addr f1 + ff_size (ff_cls f1) <= ff_addr f2 \/ ff_addr f2 + ff_size (ff_cls f2) <= ff_addr f1;
ai_fframe_block_disjoint : forall s LB FS RE m f b,
ai_run s LB FS RE m -> In f FS -> In b LB ->
ff_addr f + ff_size (ff_cls f) <= ablk_addr b \/ ablk_addr b + ablk_size b <= ff_addr f;

ai_fframe_release0 : forall c0 s LB FS RE m f (flag : word),
ai_run s LB FS RE m -> In (c0, f) FS ->
bytes_at segs m (f + ff_size c0 - 8) (le8 flag) ->
ai_run s LB (ffs_remove f FS) RE (write_to_mem m flag [Z_to_bv 8 0])
/\ wview segs m flag <> None
/\ bv_unsigned flag + 1 <= band_lo
/\ aheap_presA LB FS band_lo m (write_to_mem m flag [Z_to_bv 8 0]);

ai_fframe_flag0 : forall c0 s LB FS RE m f,
ai_run s LB FS RE m -> In (c0, f) FS ->
exists flag : word, ro_cells segs m (f + ff_size c0 - 8) [C8 flag] /\ ae_fs_base RE + 0x1000 <= bv_unsigned flag < ae_fs_base RE + 0x9000;

ai_fframes_nodup : forall s LB FS RE m, ai_run s LB FS RE m -> List.NoDup (map ff_addr FS);

ai_entry_facts : forall s LB FS RE m, ai_run s LB FS RE m ->
ae_sp0 RE - 0xa0 <= ae_stack_top RE < ae_sp0 RE + 0x8000 /\ ae_stack_top RE mod 4096 = 0
/\ appr (ae_fs_base RE) 0xb09000 /\ ae_fs_base RE + 0xb09000 <= band_lo
/\ band_lo + 0x800000 <= ae_sp0 RE
/\ ae_sp0 RE <= 0x800000000000;

ai_shadow_base : forall s LB FS RE m, ai_run s LB FS RE m -> shadow_base segs m;

ai_uar_on : forall s LB FS RE m, ai_run s LB FS RE m ->
ro_cells segs m 0x0e8210 [C8 (Z_to_bv 64 0x0f21c0)] /\ ro_cells segs m 0x0f21c0 [C4 (Z_to_bv 64 1)];

ai_rt_consts : ai_rt_consts_stmt ai_run;
ai_errno : ai_errno_stmt ai_run;
ai_errno_frame : ai_errno_frame_stmt ai_run;
ai_nbhd : ai_nbhd_stmt ai_run;

ai_malloc : forall L, amallocA_stmt ai_run L;
ai_calloc : forall L, acallocA_stmt ai_run L;
ai_free : forall L, afreeA_stmt ai_run L;
ai_free_null : afree_nullA_stmt ai_run;
ai_stack_malloc_0 : astack_mallocA_stmt ai_run 0 (ala_stack_malloc_0 AL);

ai_stack_malloc_1 : astack_mallocA_stmt ai_run 1 0x4ab30;
ai_stack_malloc_2 : astack_mallocA_stmt ai_run 2 0x4acc0;
ai_asan_memset : aasan_memsetA_stmt ai_run;
ai_set_shadow_00 : aset_shadowA_stmt ai_run (ala_set_shadow_00 AL) 0;
ai_set_shadow_f8 : aset_shadowA_stmt ai_run (ala_set_shadow_f8 AL) 0xf8
}.

Lemma ablock_rangeA_enc A n : ablock_rangeA A n -> ablock_rangeA_lia A n.
Proof.
intros ((H1 & H2) & H3 & H4 & H5 & H6). pose proof (@band_lo_range BAND) as BR.
split; [| split; [exact H3| split; [exact H4| split; [exact H5| exact H6]]]].
split; [apply appr_to_lia; [exact H4| clear - H5 BR; lia| exact H1]|].
unfold zhigh. destruct (Z.leb_spec 0x10007fff8000 A) as [K|K]; cbn [Z.b2z]; [clear - H4; lia|].
destruct (Z.le_gt_cases n 32768) as [S|S]; [specialize (H2 S); unfold KHI in H2; clear - H2 K; lia| clear - S; lia].
Qed.

End WithLayout.

Arguments aclient_addrA {BAND} AL LB FS SP a /.
Arguments aheap_presA {BAND} segs AL LB FS SP m m' /.
