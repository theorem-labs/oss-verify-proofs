(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 UI56 YI0x YL0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition LLVM : Z := ubs2_A_LLVMFuzzerTestOneInput.
Definition L_TAIL : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x198).
Definition L_NCHK : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x1f8).
Definition L_FREERET : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x208).
Definition L_RET0 : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x210).
Definition L_MAIN : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x244).
Definition L_LH : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x284).
Definition L_CLOSE : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x2bc).
Definition LLVM_FRAME : Z := 192.
Definition saved_chunks (k : nat) : list YQ0b.chunk :=
[mkChunk 184 (CVal 8 (SOff k 0)); mkChunk 176 (CVal 8 (SOff (k+1) 0)); mkChunk 168 (CVal 8 (SOff (k+2) 0));
mkChunk 160 (CVal 8 (SOff (k+3) 0)); mkChunk 152 (CVal 8 (SOff (k+4) 0)); mkChunk 144 (CVal 8 (SOff (k+5) 0));
mkChunk 136 (CVal 8 (SOff (k+6) 0)); mkChunk 128 (CVal 8 (SOff (k+7) 0)); mkChunk 120 (CVal 8 (SOff (k+8) 0));
mkChunk 112 (CVal 8 (SOff (k+9) 0))].
Definition saved_vals (regs0 : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs0 1); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22);
bv_unsigned (getr regs0 23); bv_unsigned (getr regs0 24)].
Definition saved_ok (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
word_mem ubs2segs mem (sp0 - 8) (bv_unsigned (getr regs0 1)) /\
word_mem ubs2segs mem (sp0 - 16) (bv_unsigned (getr regs0 8)) /\
word_mem ubs2segs mem (sp0 - 24) (bv_unsigned (getr regs0 9)) /\
word_mem ubs2segs mem (sp0 - 32) (bv_unsigned (getr regs0 18)) /\
word_mem ubs2segs mem (sp0 - 40) (bv_unsigned (getr regs0 19)) /\
word_mem ubs2segs mem (sp0 - 48) (bv_unsigned (getr regs0 20)) /\
word_mem ubs2segs mem (sp0 - 56) (bv_unsigned (getr regs0 21)) /\
word_mem ubs2segs mem (sp0 - 64) (bv_unsigned (getr regs0 22)) /\
word_mem ubs2segs mem (sp0 - 72) (bv_unsigned (getr regs0 23)) /\
word_mem ubs2segs mem (sp0 - 80) (bv_unsigned (getr regs0 24)).
Lemma saved_ok_frame : forall m m' sp0 regs0,
saved_ok m sp0 regs0 -> (forall a, sp0 - 80 <= a < sp0 -> mbyte ubs2segs m' a = mbyte ubs2segs m a) -> saved_ok m' sp0 regs0.
Proof.
intros m m' sp0 regs0 H Hf. unfold saved_ok in *.
repeat match goal with |- _ /\ _ => split end;
repeat match type of H with _ /\ _ => let H1 := fresh in destruct H as [H1 H] end;
first [ intros k Hk; rewrite Hf by lia;
match goal with Hx : word_mem _ m ?a _ |- mbyte _ m (?a + _) = _ => apply Hx; exact Hk end ].
Qed.
Definition untouched_ok (regs0 regs1 : bvmap 5 word) : Prop :=
getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 25 = getr regs0 25 /\ getr regs1 26 = getr regs0 26 /\ getr regs1 27 = getr regs0 27.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Definition llvm_post (regs0 : bvmap 5 word) L A mem md (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR LIB_STACK (spZ regs0) [] L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\
st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
(forall b, In b (blocks L A) -> In b (blocks L' A')).
Lemma tmp_blocks_fp : forall L A Lc Ac memc mdc (X rest : list (Z * Z)),
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (X ++ rest) ->
(forall b, In b (blocks L A) -> In b rest) ->
forall a, inFP (blocks_fp X) a ->
exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n.
Proof.
intros L A Lc Ac memc mdc X rest HH HP Hbase a (r & Hr & Ha).
unfold blocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
exists b, n. split.
{ eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin. }
split; [|lia]. intros H0. apply Hbase in H0.
destruct (in_split _ _ Hin) as (X1 & X2 & ->).
assert (HP' : Permutation (blocks Lc Ac) ((b, n) :: (X1 ++ X2) ++ rest)).
{ eapply Permutation_trans; [exact HP|]. rewrite <- !app_assoc. cbn [app].
change (X1 ++ (b, n) :: X2 ++ rest) with (X1 ++ (b, n) :: (X2 ++ rest)).
apply Permutation_sym. apply Permutation_middle. }
destruct (heap_sep_perm _ _ LAWS Lc Ac memc mdc (b, n) _ (b, n) HH HP' ltac:(apply in_app_iff; right; exact H0)) as [H1|H1]; cbn [fst snd] in H1; lia.
Qed.
Lemma cgif_at_low : forall m m' g s N Lc Ac memc mdc rest,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (cgif_blocks g s N ++ rest) ->
cgif_at m g s -> (forall a, 0 <= a < alloc_ceiling -> mbyte ubs2segs m' a = mbyte ubs2segs m a) -> cgif_at m' g s.
Proof.
intros m m' g s N Lc Ac memc mdc rest HH HB (Hg & Hr & Hf) Hlow.
assert (R : forall b n, In (b, n) (cgif_blocks g s N) -> 4096 <= b /\ b + n <= alloc_ceiling).
{ intros b n Hin. eapply (blocks_range _ _ LAWS); [exact HH|]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hin. }
unfold cgif_blocks in R.
split; [|split].
- destruct (R g CGIF_SIZE ltac:(left; reflexivity)) as [R1 R2]. unfold CGIF_SIZE in R2.
eapply obj_at_transport_range; [exact Hg | exact (proj1 LAY_CGIF_ok) |]. intros i Hi. unfold CGIF_SIZE in Hi. apply Hlow. lia.
- destruct (R (cg_raw s) RAW_SIZE ltac:(right; left; reflexivity)) as [R1 R2]. unfold RAW_SIZE in R2.
eapply obj_at_transport_range; [exact Hr | exact (proj1 LAY_Raw_ok) |]. intros i Hi. unfold RAW_SIZE in Hi. apply Hlow. lia.
- intros f Hin.
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s N)).
{ unfold cgif_blocks. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin|]. left. reflexivity. }
destruct (R (fr_ptr f) FRAME_SIZE Hfb) as [R1 R2]. unfold FRAME_SIZE in R2.
eapply obj_at_transport_range; [exact (Hf f Hin) | exact (proj1 LAY_Frame_ok) |]. intros i Hi. unfold FRAME_SIZE in Hi. apply Hlow. lia.
Qed.
Lemma cgif_at_kept : forall m m' g s N (bl rest : list (Z * Z)),
Permutation bl (cgif_blocks g s N ++ rest) ->
cgif_at m g s -> (forall b n i, In (b, n) bl -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs m (b + i)) ->
cgif_at m' g s.
Proof.
intros m m' g s N bl rest HB (Hg & Hr & Hf) Hkeep.
assert (K : forall b n, In (b, n) (cgif_blocks g s N) -> forall i, 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs m (b + i)).
{ intros b n Hin i Hi. apply (Hkeep b n i); [|exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hin. }
unfold cgif_blocks in K.
split; [|split].
- eapply obj_at_transport_range; [exact Hg | exact (proj1 LAY_CGIF_ok) |]. apply (K g CGIF_SIZE). left. reflexivity.
- eapply obj_at_transport_range; [exact Hr | exact (proj1 LAY_Raw_ok) |]. apply (K (cg_raw s) RAW_SIZE). right. left. reflexivity.
- intros f Hin. eapply obj_at_transport_range; [exact (Hf f Hin) | exact (proj1 LAY_Frame_ok) |]. apply (K (fr_ptr f) FRAME_SIZE).
right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
Qed.
End S.
End c.
Ltac ew_havocA :=
repeat match goal with
| |- context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) by nat_lt_lit
end.
Ltac ew_havocA_in H :=
repeat match type of H with
| context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) in H by nat_lt_lit
end.
Ltac mem_back1 bases slv :=
match goal with
| HF : frame_of ?E ?rs ?m ?m' |- mbyte _ ?m' ?a = _ =>
mb_frame_with HF slv ltac:(ew_havocA; bases; slv)
| Hout : (forall x : word, bv_unsigned x < ?d \/ ?d + ?n <= bv_unsigned x -> ?m' x = ?m x) |- mbyte ?sg ?m' ?a = _ =>
unfold mbyte at 1; rewrite (Hout (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by slv; slv); fold (mbyte sg m a)
| Hhi : (forall x : Z, alloc_ceiling <= x < 2 ^ 64 -> ~ _ -> mbyte _ ?m' x = mbyte _ ?m x /\ _) |- mbyte _ ?m' ?a = _ =>
rewrite (proj1 (Hhi a ltac:(slv) ltac:(slv)))
| Hfr : (forall x : Z, alloc_ceiling <= x < 2 ^ 64 -> ~ _ -> ~ _ -> ~ _ -> mbyte _ ?m' x = mbyte _ ?m x) |- mbyte _ ?m' ?a = _ =>
rewrite (Hfr a ltac:(slv) ltac:(slv) ltac:(slv) ltac:(slv))
| Hq : (forall x : Z, alloc_ceiling <= x < 2 ^ 64 -> ~ _ -> mbyte _ ?m' x = mbyte _ ?m x) |- mbyte _ ?m' ?a = _ =>
rewrite (Hq a ltac:(slv) ltac:(slv))
end.
Ltac mem_back bases slv := cbn [ms_mem mkst] in *; repeat (reflexivity || mem_back1 bases slv).
