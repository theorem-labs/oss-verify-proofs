(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qk8e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qk8e.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qk8e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qk8e.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKJh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKJh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxCw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjWq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjWq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh.
Import QCiC.Mq1.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition pextA : Type := unit.
Definition pextA_init : pextA := tt.

Record PStateA := mkPSA {
ps_a  : AState;
ps_xa : pextA;
ps_soa : stdout_st
}.
Definition set_a (v : AState) (s : PStateA) := mkPSA v (ps_xa s) (ps_soa s).
Definition set_xa (v : pextA) (s : PStateA) := mkPSA (ps_a s) v (ps_soa s).
Definition set_soa (v : stdout_st) (s : PStateA) := mkPSA (ps_a s) (ps_xa s) v.

Definition psA_init : PStateA := mkPSA astate0 pextA_init stdout_init.

Local Notation MP := (Qpj5.Mq1.M PStateA).

Definition mspin {St A} : Qpj5.Mq1.M St A := msys NSetTid (fun _ => None).

Definition PROT_RW : Z := 3.
Definition FL_ANON : Z := 34.
Definition FL_FIXED : Z := 50.
Definition FL_FIXED_NR : Z := 16434.

Definition grant_ceil : Z := sp_window_hi - stack_max_size.
Lemma grant_ceil_val : grant_ceil = 0x7fffff800000. Proof. reflexivity. Qed.
Definition grant_ok (len a : Z) : bool :=
(a mod page_size =? 0) && (0 <? a) && (a + mmap_len len <=? grant_ceil).

Definition is_enomem (r : word) : bool := bv_eqb r (errno_ret ENOMEM).

Definition sh_lo (a : Z) : Z := kShadowOffset + a / 8.
Definition sh_hi (a n : Z) : Z := kShadowOffset + (a + n - 1) / 8 + 1.
Definition wshape_ok (a n : Z) (ws : list (word * list byte)) : bool :=
forallb (fun w => (sh_lo a <=? bv_unsigned (fst w)) && (bv_unsigned (fst w) <? sh_hi a n)
&& (length (snd w) =? 1)%nat) ws.

Fixpoint zrange (lo : Z) (k : nat) : list Z :=
match k with O => [] | S k' => lo :: zrange (lo + 1) k' end.
Fixpoint zlist_eqb (l1 l2 : list Z) : bool :=
match l1, l2 with
| [], [] => true
| x :: l1', y :: l2' => (x =? y) && zlist_eqb l1' l2'
| _, _ => false
end.
Definition wcover_ok (a n : Z) (ws : list (word * list byte)) : bool :=
zlist_eqb (map (fun w => bv_unsigned (fst w)) ws) (zrange (sh_lo a) (Z.to_nat (sh_hi a n - sh_lo a))).

Definition dec_anonA (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option ansA :=
match rsp with
| mkEffectU r [] [] [] [] [] => if is_enomem r then Some AErr else None
| mkEffectU r ws [(a, n)] [] [] [] =>
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && grant_ok len (bv_unsigned r)
&& avoids (bv_unsigned r) (mmap_len len) avoid && wshape_ok (bv_unsigned r) (mmap_len len) ws
&& wcover_ok (bv_unsigned r) (mmap_len len) ws
then Some (AOk (bv_unsigned r)) else None
| _ => None
end.

Lemma zlist_eqb_eq l1 l2 : zlist_eqb l1 l2 = true <-> l1 = l2.
Proof.
revert l2. induction l1 as [|x l1 IH]; intros [|y l2]; cbn; try (split; [discriminate| discriminate]); [tauto|].
rewrite Bool.andb_true_iff, Z.eqb_eq, IH. split; [intros [-> ->]; reflexivity| intros H; injection H; auto].
Qed.

Definition dec_fixedA_full (addr len : Z) (rsp : resp) : option ansA :=
match rsp with
| mkEffectU r [] [] [] [] [] => if is_enomem r then Some AErr else None
| mkEffectU r [] [(a, n)] [] [] [] =>
if bv_eqb r (Z_to_bv 64 addr) && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
then Some (AOk addr) else None
| _ => None
end.

Definition dec_fixedA (addr len : Z) (rsp : resp) : option ansA :=
match rsp with
| mkEffectU r [] [(a, n)] [] [] [] =>
if bv_eqb r (Z_to_bv 64 addr) && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
then Some (AOk addr) else None
| _ => None
end.

Definition dec_remapA (addr len : Z) (rsp : resp) : option ansA := dec_fixedA_full addr len rsp.

Definition ucover_ok (a n : Z) (us : list (word * word)) : bool :=
forallb (fun u => (sh_lo a <=? bv_unsigned (fst u)) && (bv_unsigned (fst u) + bv_unsigned (snd u) <=? sh_hi a n)) us.
Definition dec_munmapA (addr len : Z) (rsp : resp) : option ansA :=
match rsp with
| mkEffectU r [] [] ((a, n) :: us) [] [] =>
if (bv_unsigned r =? 0) && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
&& ucover_ok addr (mmap_len len) us
then Some (AOk 0) else None
| _ => None
end.

Lemma dec_anonA_err_inv len avoid rsp :
dec_anonA len avoid rsp = Some AErr -> rsp = mkEffectU (errno_ret ENOMEM) [] [] [] [] [].
Proof.
destruct rsp as [r [|w ws] [|[a n] [|z zs]] [|u us] [|c cs] [|i iz]]; cbn; try discriminate;
try (destruct (is_enomem r) eqn:E; [| discriminate]; intros _; unfold is_enomem in E; apply Fs.bv_eqb_eq in E; subst; reflexivity);
destruct (_ && _); discriminate.
Qed.

Lemma dec_anonA_ok_inv len avoid rsp x :
dec_anonA len avoid rsp = Some (AOk x) ->
exists ws, rsp = mkEffectU (Z_to_bv 64 x) ws [(Z_to_bv 64 x, Z_to_bv 64 (mmap_len len))] [] [] [] /\
x = bv_unsigned (eff_ret rsp) /\ grant_ok len x = true /\ avoids x (mmap_len len) avoid = true /\ wshape_ok x (mmap_len len) ws = true
/\ map (fun w => bv_unsigned (fst w)) ws = zrange (sh_lo x) (Z.to_nat (sh_hi x (mmap_len len) - sh_lo x)).
Proof.
destruct rsp as [r ws [|[a n] [|z zs]] [|u us] [|c cs] [|i iz]]; cbn; try discriminate;
try (destruct ws; [destruct (is_enomem r)|]; discriminate).
all: try (destruct ws; discriminate).
destruct (bv_eqb a r) eqn:E1; [|cbn; try (destruct ws; discriminate); discriminate].
destruct (bv_eqb n (Z_to_bv 64 (mmap_len len))) eqn:E2; [|cbn; try (destruct ws; discriminate); discriminate].
destruct (grant_ok len (bv_unsigned r)) eqn:E3; [|cbn; try (destruct ws; discriminate); discriminate].
destruct (avoids (bv_unsigned r) (mmap_len len) avoid) eqn:E4; [|cbn; try (destruct ws; discriminate); discriminate].
destruct (wshape_ok (bv_unsigned r) (mmap_len len) ws) eqn:E5; [|cbn; try (destruct ws; discriminate); discriminate].
destruct (wcover_ok (bv_unsigned r) (mmap_len len) ws) eqn:E6; [|cbn; try (destruct ws; discriminate); discriminate].
unfold wcover_ok in E6. apply zlist_eqb_eq in E6.
cbn. intros H. assert (x = bv_unsigned r) as -> by (destruct ws; injection H; auto).
apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. subst.
exists ws. rewrite Z_to_bv_bv_unsigned. repeat split; auto.
Qed.

Lemma dec_fixedA_noerr addr len rsp : dec_fixedA addr len rsp <> Some AErr.
Proof.
destruct rsp as [r [|w ws] [|[a n] [|z zs]] [|u us] [|c cs] [|i iz]]; cbn; try discriminate.
destruct (_ && _); discriminate.
Qed.

Lemma dec_fixedA_ok_inv addr len rsp x :
dec_fixedA addr len rsp = Some (AOk x) ->
x = addr /\ rsp = mkEffectU (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] [] [].
Proof.
destruct rsp as [r [|w ws] [|[a n] [|z zs]] [|u us] [|c cs] [|i iz]]; cbn; try discriminate.
- destruct (bv_eqb r (Z_to_bv 64 addr)) eqn:E1; [|discriminate]. destruct (bv_eqb a (Z_to_bv 64 addr)) eqn:E2; [|discriminate].
destruct (bv_eqb n (Z_to_bv 64 (mmap_len len))) eqn:E3; [|discriminate]. cbn. intros H. injection H as <-.
apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. apply Fs.bv_eqb_eq in E3. subst. auto.
Qed.

Lemma dec_munmapA_inv addr len rsp x :
dec_munmapA addr len rsp = Some x ->
x = AOk 0 /\ exists us, rsp = mkEffectU (eff_ret rsp) [] [] ((Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len)) :: us) [] [] /\ bv_unsigned (eff_ret rsp) = 0
/\ ucover_ok addr (mmap_len len) us = true.
Proof.
destruct rsp as [r [|w ws] [|z zs] [|[a n] us] [|c cs] [|i iz]]; cbn -[ucover_ok]; try discriminate.
destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. destruct (bv_eqb a (Z_to_bv 64 addr)) eqn:E1; [|discriminate].
destruct (bv_eqb n (Z_to_bv 64 (mmap_len len))) eqn:E2; [|discriminate]. destruct (ucover_ok addr (mmap_len len) us) eqn:E3; [|discriminate].
cbn. intros H. injection H as <-.
apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. subst. split; [reflexivity|]. exists us. auto.
Qed.

Definition ev_stepA (e : evA) : MP ansA :=
match e with
| EvMapAnon len avoid => msys (NMmap 0 len PROT_RW FL_ANON) (dec_anonA len avoid)
| EvMapFixed addr len => msys (NMmap addr len PROT_RW FL_FIXED) (dec_fixedA addr len)
| EvRemap addr len => msys (NMmap addr len PROT_RW FL_FIXED_NR) (dec_remapA addr len)
| EvMunmap addr len => msys (NMunmap addr len) (dec_munmapA addr len)
end.

Fixpoint membedA {R} (t : T R) : MP R :=
match t with
| SRet (ROk r) => mret r
| SRet RSpin => mspin
| SRet (RUnr _) => munr
| SVis e k => a <- ev_stepA e ;; membedA (k a)
end.

Section WithLayout.
Variable L : ALay.

Definition raw_malloc_A (n : Z) : MP (option aptr) :=
s <- mget ;;
'(r, a') <- membedA (asan_malloc L (ps_a s) n) ;;
mupd (set_a a') ;;;
mret r.

Definition raw_calloc_A (m k : Z) : MP (option aptr) :=
s <- mget ;;
'(r, a') <- membedA (asan_calloc L (ps_a s) m k) ;;
mupd (set_a a') ;;;
mret r.

Definition raw_free_A (p : aptr) : MP unit :=
s <- mget ;;
a' <- membedA (asan_free L (ps_a s) p) ;;
mupd (set_a a').

Definition ptr_addr_A (s : PStateA) (p : aptr) : Z :=
match p with
| ASec map_beg _ => map_beg + kSecUserOff
| APrim _ _ => 0
end.

Fixpoint interpA {A} (t : aprog aptr A) : MP A :=
match t with
| ARet a => mret a
| AUnr => munr
| AMalloc n k => mbind (raw_malloc_A n) (fun r => interpA (k r))
| AFree p k => mbind (raw_free_A p) (fun _ => interpA k)
end.

Definition io_A : IOStyle PStateA := io_S ps_soa set_soa.

Definition alloc_init_noneA (bitmap : Z) : MP unit := mret tt.
Definition alloc_count_zeroA : MP Z := mret 0.

Section WithTables.
Variable TAB : ftables.

Variable stageA : Z.

Definition fuzz_MA (data : list Z) : MP Z :=
interpA (fuzz_one TAB (FUEL (zlength data / 4)) data).

Definition run_A (cfg : Z) (payload : list Z) : MP Z :=
target_run raw_malloc_A raw_free_A (io_emit io_A) fuzz_MA cfg payload.

Definition main_A (argv : list (list Z)) : MP Empty_set :=
code <- main_model io_A raw_malloc_A raw_free_A stageA alloc_init_noneA run_A alloc_count_zeroA argv ;;
exit_model io_A code.

Definition argv_ZA (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.

Definition prog_A (argv : list (list byte)) (s0 : PStateA) : itree node (exc unit) :=
ebind (main_A (argv_ZA argv) s0) (fun p => match fst p : Empty_set with end).

End WithTables.
End WithLayout.
