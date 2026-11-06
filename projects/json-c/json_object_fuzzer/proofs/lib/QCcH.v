(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition blk : Type := (Z * Z)%type.
Definition blk_addr (b : blk) : Z := fst b.
Definition blk_size (b : blk) : Z := snd b.

Definition in_block (LB : list blk) (a : Z) : Prop :=
exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

Fixpoint lb_remove (p : Z) (LB : list blk) : list blk :=
match LB with
| [] => []
| b :: LB' => if Z.eqb (blk_addr b) p then LB' else b :: lb_remove p LB'
end.

Fixpoint lb_size (p : Z) (LB : list blk) : option Z :=
match LB with
| [] => None
| b :: LB' => if Z.eqb (blk_addr b) p then Some (blk_size b) else lb_size p LB'
end.

Definition ENOMEMv : Z := 12.

Record heap_layout := HL {
hl_segs : list Segment;
hl_malloc : Z;  hl_free : Z;  hl_calloc : Z;  hl_realloc : Z;
hl_malloc2 : Z; hl_free2 : Z;
hl_tp : Z;
hl_got_guard : Z; hl_guard : Z;
hl_auxv : Z;
hl_libc : Z;
hl_volatile : Z -> Prop;
hl_stack : Z;
hl_client_static : Z -> Prop;
hl_scratch : Z -> Prop;
hl_consts : list (Z * list byte);
hl_img_lo : Z; hl_img_hi : Z;
hl_static_in_img : forall a, hl_client_static a -> hl_img_lo <= a < hl_img_hi;
hl_img_range : 0 <= hl_img_lo /\ hl_img_hi <= alloc_ceiling;
hl_scratch_in_img : forall a, hl_scratch a -> hl_img_lo <= a < hl_img_hi;
hl_scratch_not_static : forall a, hl_scratch a -> ~ hl_client_static a;
hl_consts_ok : forall c a, In c hl_consts -> fst c <= a < fst c + Z.of_nat (length (snd c)) ->
~ hl_client_static a /\ ~ hl_scratch a /\ hl_img_lo <= a < hl_img_hi
}.

Section Iface.
Variable L : heap_layout.
Notation segs := (hl_segs L).
Notation errno_a := (hl_tp L - 164).

Definition client_addr (LB : list blk) (SP : Z) (a : Z) : Prop :=
SP <= a \/ hl_client_static L a \/ in_block LB a.

Definition heap_pres (LB : list blk) (SP : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> client_addr LB SP a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Definition model_vm_only (md md' : Model) : Prop :=
m_fd md' = m_fd md /\ m_io md' = m_io md /\ m_fsys md' = m_fsys md /\
m_proc md' = m_proc md /\ m_lim md' = m_lim md /\ m_time md' = m_time md /\
vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md).

#[using="Type"] Lemma model_vm_only_refl : forall md, model_vm_only md md.
Proof. intros; repeat split; reflexivity. Qed.
#[using="Type"] Lemma model_vm_only_trans : forall a b c, model_vm_only a b -> model_vm_only b c -> model_vm_only a c.
Proof. intros a b c H1 H2. unfold model_vm_only in *. intuition congruence. Qed.

Definition ret_state (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0' : word) (m' : word -> option byte) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs).

Definition FSAVED : list Z := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition fsaved (F F' : bvmap 5 word) : Prop :=
forall k, In k FSAVED -> Sem.reg_get F' (Z_to_bv 5 k) = Sem.reg_get F (Z_to_bv 5 k).
Definition frm0 (fc : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned fc) 5) 7 = 0%Z.
Definition ret_statew (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0' : word) (m' : word -> option byte) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom segs)
/\ fsaved F F' /\ (frm0 fc -> frm0 fc').

#[using="Type"] Lemma fsaved_refl : forall F, fsaved F F. Proof. intros F k _; reflexivity. Qed.
#[using="Type"] Lemma fsaved_trans : forall F1 F2 F3, fsaved F1 F2 -> fsaved F2 F3 -> fsaved F1 F3.
Proof. intros F1 F2 F3 H1 H2 k Hk. rewrite (H2 k Hk). apply H1. exact Hk. Qed.
#[using="Type"] Lemma fsaved_set_self : forall F (k : bv 5), fsaved F (bvmap_set k (Sem.reg_get F k) F).
Proof.
intros F k j Hj. destruct (Z.eq_dec (bv_unsigned k) (bv_unsigned (Z_to_bv 5 j))) as [E|NE].
- replace (Z_to_bv 5 j) with k by (apply bv_eq; exact E). apply QEpW.reg_get_set_same.
- apply QEpW.reg_get_set_other. intros E. apply NE. rewrite E. reflexivity.
Qed.
#[using="Type"] Lemma fsaved_set_self' : forall F (k1 k2 : bv 5), bv_unsigned k1 = bv_unsigned k2 -> fsaved F (bvmap_set k1 (Sem.reg_get F k2) F).
Proof. intros F k1 k2 E. replace k2 with k1 by (apply bv_eq; exact E). apply fsaved_set_self. Qed.
#[using="Type"] Lemma ret_statew_same : forall ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m',
ret_statew ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m'
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom segs)).
Proof. intros. unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [apply fsaved_refl | intros H; exact H]. Qed.
#[using="Type"] Lemma ret_statew_of_exact : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m' ms',
ret_state ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m' ms' ->
ret_statew ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m' ms'.
Proof. intros until ms'. intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). apply ret_statew_same. Qed.

#[using="Type"] Lemma ret_statew_intro : forall ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F F' fc fc' m',
fsaved F F' -> (frm0 fc -> frm0 fc') ->
ret_statew ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m'
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom segs)).
Proof. intros. unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; assumption. Qed.

Record heap_iface := HI {
AS : Type;
HEAP : AS -> list blk -> (word -> option byte) -> Model -> Prop;

hi_top : Z;
hi_top_hi : alloc_ceiling < hi_top;

heap_model_ok : forall A LB m md, HEAP A LB m md -> model_ok md;
heap_mem_inv : forall A LB m md, HEAP A LB m md -> mem_inv segs m;
heap_blk : forall A LB m md a n, HEAP A LB m md -> In (a, n) LB ->
0 <= n /\ a mod 16 = 0 /\ 0 < a /\ a + n <= alloc_ceiling /\ wr_at segs m a n;
heap_blk_img : forall A LB m md a n, HEAP A LB m md -> In (a, n) LB ->
a + n <= hl_img_lo L \/ hl_img_hi L <= a;
heap_blk_disjoint : forall A LB m md a n a' n', HEAP A LB m md ->
In (a, n) LB -> In (a', n') LB -> a <> a' -> (a + n <= a' \/ a' + n' <= a);
heap_blk_nodup : forall A LB m md, HEAP A LB m md -> List.NoDup (map blk_addr LB);
heap_blk_not_static : forall A LB m md a n i, HEAP A LB m md -> In (a, n) LB ->
0 <= i < n -> ~ hl_client_static L (a + i);
heap_perm : forall A LB LB' m md, HEAP A LB m md -> Permutation LB LB' -> HEAP A LB' m md;

heap_blk_slack : forall A LB m md a n, HEAP A LB m md -> In (a, n) LB ->
exists junk, bytes_at segs m (a + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16;

heap_model_frame : forall A LB m md md', HEAP A LB m md ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md ->
m_halted md' = None -> HEAP A LB m md';

heap_frame : forall A LB m m' md, HEAP A LB m md ->
(forall a, 0 <= a < 2^64 -> ~ (client_addr LB alloc_ceiling a /\ a < hi_top) -> ~ hl_scratch L a -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
mem_inv segs m' ->
HEAP A LB m' md;

heap_canary : forall A LB m md, HEAP A LB m md ->
exists g : word,
bytes_at segs m (hl_got_guard L) (le8 (Z_to_bv 64 (hl_guard L))) /\
bytes_at segs m (hl_guard L) (le8 g) /\
bytes_at segs m (hl_tp L - 16) (le8 g);

heap_auxv : forall A LB m md, HEAP A LB m md ->
exists (aw : Z) (keys : list Z),
(bytes_at segs m (hl_auxv L) (le8 (Z_to_bv 64 aw)) /\ aw mod 8 = 0 /\
Forall (fun k => 0 < k < 2^64 /\ k <> 33) keys /\
(forall i k, nth_error keys i = Some k -> bytes_at segs m (aw + 16 * Z.of_nat i) (le8 (Z_to_bv 64 k))) /\
bytes_at segs m (aw + 16 * Z.of_nat (length keys)) (le8 (Z_to_bv 64 0))) /\

hi_top <= aw;

heap_need_locks : forall A LB m md, HEAP A LB m md -> bytes_at segs m (hl_libc L + 3) [Z_to_bv 8 0];

heap_consts : forall A LB m md, HEAP A LB m md -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (hl_consts L);

hi_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS) (LB : list blk) (n lo : Z) (errv : word),
HEAP A LB m md ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres LB (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAP A' LB m' md')
\/ (r <> 0 /\ (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])
/\ HEAP A' ((r, n) :: LB) m' md') ) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc L)) fc None m (seg_rom segs)) md) T;

hi_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS) (LB : list blk) (p lo : Z) (errv : word),
HEAP A LB m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p ->
(forall ms' m' md' A' (r : word),
ret_state ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAP A' (lb_remove p LB) m' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free L)) fc None m (seg_rom segs)) md) T;

hi_malloc2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS) (LB : list blk) (n lo : Z) (errv : word),
HEAP A LB m md ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres LB (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAP A' LB m' md')
\/ (r <> 0 /\ (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])
/\ HEAP A' ((r, n) :: LB) m' md') ) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc2 L)) fc None m (seg_rom segs)) md) T;

hi_free2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS) (LB : list blk) (p lo : Z) (errv : word),
HEAP A LB m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p ->
(forall ms' m' md' A' (r : word),
ret_state ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAP A' (lb_remove p LB) m' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free2 L)) fc None m (seg_rom segs)) md) T;

hi_calloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS) (LB : list blk) (cnt sz lo : Z) (errv : word),
HEAP A LB m md ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 1 <= cnt * sz < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres LB (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAP A' LB m' md')
\/ (r <> 0 /\ rw_cells segs m' r [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
/\ HEAP A' ((r, cnt * sz) :: LB) m' md') ) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_calloc L)) fc None m (seg_rom segs)) md) T;

hi_realloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS) (LB : list blk) (p n0 n lo : Z) (errv : word) (old : list byte) (junk0 : list byte),
HEAP A LB m md -> In (p, n0) LB ->
rw_cells segs m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ heap_pres LB (bv_unsigned sp) m m' /\ HEAP A' LB m' md')
\/ (r <> 0 /\ heap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ (exists junk, rw_cells segs m' r
[CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)])
/\ HEAP A' ((r, n) :: lb_remove p LB) m' md') ) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc L)) fc None m (seg_rom segs)) md) T
}.

End Iface.

End RC__1.
