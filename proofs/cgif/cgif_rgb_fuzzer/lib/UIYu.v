(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n
YI00 YI02 YI01 YI07 YI03 YI04 YI06 YI5a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rst_memset_spec : memset_spec ubs2_msyms ubs2_A_memset.
Proof using. exact ubs2_memset. Qed.
Lemma rst_U_tisz : forall E n idl,
ew E n = Z_to_bv 64 idl -> 2 <= idl <= 256 ->
U E (SAlu ALU_SLL (SMd M_MUL (SOff n 0) (SOff n 0)) (SLit 1)) = 2 * idl * idl.
Proof using.
intros E n idl Hn Hidl.
assert (Hsq : idl * idl <= 256 * 256) by nia. assert (Hsq0 : 0 <= idl * idl) by nia.
rewrite (U_sll1_small E _ (idl * idl)); [lia | | lia | lia].
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n idl Hn) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Definition rst_stk : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition rst_gchunks : list YQ0b.chunk :=
[ mkChunk 0 (CVal 8 (SOff 32%nat 0)); mkChunk 8 (CVal 8 (SOff 33%nat 0)); mkChunk 16 (CVal 8 (SOff 34%nat 0));
mkChunk 24 (CVal 8 (SOff 35%nat 0)); mkChunk 40 (CVal 8 (SOff 36%nat 0)); mkChunk 60 (CVal 4 (SOff 37%nat 0)) ].
Definition rst_greg : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 0 72 60 68 rst_gchunks.
Definition rst_slot : YQ0b.region := regw 38 2.
Definition rst_atoms : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + 16) (2 ^ 63) 4); (10%nat, mkAF 4096 CEIL_MAX 4); (11%nat, mkAF 2 256 0);
(36%nat, mkAF 4096 CEIL_MAX 4); (37%nat, mkAF 0 (2 ^ 31 - 1) 0); (38%nat, mkAF 4096 CEIL_MAX 1) ].
Definition rst_conds : list acond := [ mkAC BC_GEU (SOff 38%nat 0) (SOff 36%nat 0) ].
Definition rst_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 36%nat 0) (SAlu ALU_SLL (SOff 37%nat 0) (SLit 1)), SOff 38%nat 0) ].
Definition ss_rst : sstate :=
mkSS ubs2_A_resetDict sr_atoms [ rst_stk; rst_greg; rst_slot ] None (mkFacts rst_atoms rst_conds rst_alias).
Definition rst_sep (x nx y ny : Z) : Prop := x + nx <= y \/ y + ny <= x.
Lemma rst_nodup6 : forall a b c d e f : Z, NoDup [a; b; c; d; e; f] ->
a <> b /\ a <> c /\ a <> d /\ a <> e /\ a <> f /\ b <> c /\ b <> d /\ b <> e /\ b <> f /\
c <> d /\ c <> e /\ c <> f /\ d <> e /\ d <> f /\ e <> f.
Proof using.
intros a b c d e f H. apply NoDup_ListNoDup in H.
apply NoDup_cons_iff in H as [Ha H]. apply NoDup_cons_iff in H as [Hb H]. apply NoDup_cons_iff in H as [Hc H].
apply NoDup_cons_iff in H as [Hd H]. apply NoDup_cons_iff in H as [He _].
cbn [In] in Ha, Hb, Hc, Hd, He.
repeat split; intro Heq; subst; intuition.
Qed.
Lemma rst_mb : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte ubs2segs m' a = mbyte ubs2segs m a.
Proof using. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma rst_out : forall (m m' : word -> option byte) d n a,
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> m' x = m x) ->
0 <= a < 2 ^ 64 -> a < d \/ d + n <= a -> mbyte ubs2segs m' a = mbyte ubs2segs m a.
Proof using. intros m m' d n a H Ha Hd. apply rst_mb. apply H. rewrite unsigned_lit_small by lia. exact Hd. Qed.
Lemma rst_frame3 : forall E (r1 r2 r3 : YQ0b.region) (m m' : word -> option byte) a,
frame_of E [r1; r2; r3] m m' -> 0 <= a < 2 ^ 64 ->
~ (base_val E (r_base r1) + r_wlo r1 <= a < base_val E (r_base r1) + r_whi r1) ->
~ (base_val E (r_base r2) + r_wlo r2 <= a < base_val E (r_base r2) + r_whi r2) ->
~ (base_val E (r_base r3) + r_wlo r3 <= a < base_val E (r_base r3) + r_whi r3) ->
mbyte ubs2segs m' a = mbyte ubs2segs m a.
Proof using.
intros E r1 r2 r3 m m' a HF Ha H1 H2 H3. apply rst_mb. apply HF. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; tauto.
Qed.
Lemma rst_chunk_val : forall E ss ms i r off (n : BinNums.N) e v a b,
st_ok ubs2segs E ss ms -> nth_error (ss_mem ss) i = Some r -> In (mkChunk off (CVal n e)) (r_chunks r) ->
base_val E (r_base r) = b -> a = b + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem ubs2segs (ms_mem ms) a (N.to_nat n) v.
Proof using.
intros E ss ms i r off n e v a b HS Hi Hin Hb Ha He Hv Hn. subst a b.
destruct (st_ok_mem_ok ubs2segs E ss ms HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as HR.
destruct HR as (_ & _ & _ & Hcs).
eapply val_of_chunk_ok; [exact (proj1 (Forall_forall _ _) Hcs _ Hin) | exact He | exact Hv | exact Hn].
Qed.
Definition rst_cs : list reg := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma rst_regs_pres : forall regs regs' : bvmap 5 word,
(forall r, In r rst_cs -> getr regs' r = getr regs r) -> regs_preserved regs regs'.
Proof using.
intros regs regs' H r Hr. apply H. unfold rst_cs. apply in_map. unfold callee_saved in Hr. cbn [In]. lia.
Qed.
Lemma rst_cs_clob : forall r, In r rst_cs -> reg_in r MEMSET_CLOB = false.
Proof using.
intros r Hr. assert (Hb : forallb (fun r => negb (reg_in r MEMSET_CLOB)) rst_cs = true) by (vm_compute; reflexivity).
apply negb_true_iff. exact (proj1 (forallb_forall _ _) Hb r Hr).
Qed.
End c.
