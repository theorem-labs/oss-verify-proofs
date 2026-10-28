(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r YI0o
UI1w UI21 UI5o UI5l YI6b YL0g
YI16 YI14 UI5c YI00 UI22 UI2u UI0l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition LLVM : Z := ubs0_A_LLVMFuzzerTestOneInput.
Definition L_TAIL : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0x98).
Definition L_NCHK : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0xdc).
Definition L_FREERET : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0xf4).
Definition L_RET0 : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0xfc).
Definition L_MAIN : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0x118).
Definition L_LH : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0x158).
Definition L_CLOSE : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0x190).
Definition L_UNLINK : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0x1ac).
Lemma path_ltb_irrefl : forall p, Fs.path_ltb p p = false.
Proof using.
induction p as [|x p IH]; [reflexivity|]. cbn [Fs.path_ltb]. rewrite IH, Bool.andb_false_r, Bool.orb_false_r.
unfold bv_ltu. apply Z.ltb_irrefl.
Qed.
Lemma fs_lt_head_keys : forall r a, Fs.fs_sorted r = true -> Fs.fs_lt_head a r = true -> Forall (fun qd => fst qd <> a) r.
Proof using.
induction r as [|[q d] r IH]; intros a Hs Hh; [constructor|].
rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hq Hr]. cbn [Fs.fs_lt_head] in Hh.
constructor.
- cbn [fst]. intros ->. rewrite path_ltb_irrefl in Hh. discriminate Hh.
- apply IH; [exact Hr|]. destruct r as [|[q' d'] r']; [reflexivity|]. cbn [Fs.fs_lt_head] in Hq |- *. exact (Fs.path_ltb_trans _ _ _ Hh Hq).
Qed.
Lemma fs_lookup_remove_sorted : forall fs p, Fs.fs_sorted fs = true -> Fs.fs_lookup (Fs.fs_remove fs p) p = None.
Proof using.
induction fs as [|[q d] r IH]; intros p Hs; [reflexivity|].
rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hq Hr]. cbn [Fs.fs_remove].
destruct (Fs.path_eqb p q) eqn:E.
- apply Fs.path_eqb_eq in E. subst q. apply Fs.fs_lookup_none_of_keys. exact (fs_lt_head_keys r p Hr Hq).
- cbn [Fs.fs_lookup]. rewrite E. apply IH. exact Hr.
Qed.
Definition LLVM_FRAME : Z := 144.
Definition saved_chunks (k : nat) : list YP09.chunk :=
[mkChunk 136 (CVal 8 (SOff k 0)); mkChunk 128 (CVal 8 (SOff (k+1) 0)); mkChunk 120 (CVal 8 (SOff (k+2) 0));
mkChunk 112 (CVal 8 (SOff (k+3) 0))].
Definition saved_vals (regs0 : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs0 1); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18)].
Definition saved_ok (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
word_mem ubs0segs mem (sp0 - 8) (bv_unsigned (getr regs0 1)) /\
word_mem ubs0segs mem (sp0 - 16) (bv_unsigned (getr regs0 8)) /\
word_mem ubs0segs mem (sp0 - 24) (bv_unsigned (getr regs0 9)) /\
word_mem ubs0segs mem (sp0 - 32) (bv_unsigned (getr regs0 18)).
Lemma saved_ok_frame : forall m m' sp0 regs0,
saved_ok m sp0 regs0 -> (forall a, sp0 - 32 <= a < sp0 -> mbyte ubs0segs m' a = mbyte ubs0segs m a) -> saved_ok m' sp0 regs0.
Proof using.
intros m m' sp0 regs0 H Hf. unfold saved_ok in *.
repeat match goal with |- _ /\ _ => split end;
repeat match type of H with _ /\ _ => let H1 := fresh in destruct H as [H1 H] end;
first [ intros k Hk; rewrite Hf by lia;
match goal with Hx : word_mem _ m ?a _ |- mbyte _ m (?a + _) = _ => apply Hx; exact Hk end ].
Qed.
Definition untouched_ok (regs0 regs1 : bvmap 5 word) : Prop :=
getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 19 = getr regs0 19 /\ getr regs1 20 = getr regs0 20 /\ getr regs1 21 = getr regs0 21 /\
getr regs1 22 = getr regs0 22 /\ getr regs1 23 = getr regs0 23 /\ getr regs1 24 = getr regs0 24 /\
getr regs1 25 = getr regs0 25 /\ getr regs1 26 = getr regs0 26 /\ getr regs1 27 = getr regs0 27.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition llvm_post (regs0 : bvmap 5 word) L A mem md (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR LIB_STACK (spZ regs0) [] L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\
st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
(forall b, In b (blocks L A) -> In b (blocks L' A')).
Definition llvm_postV (regs0 : bvmap 5 word) L A mem md (PAYLOAD : list Z) (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR LIB_STACK (spZ regs0) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\
st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
sink_none ubs0_msyms mem' md' /\
(forall b, In b (blocks L A) -> In b (blocks L' A')) /\
(Fs.fs_sorted (m_fs md) = true -> ff_key (Fs.fs_lookup (m_fs md) sink_path) PAYLOAD (Fs.fs_lookup (m_fs md') sink_path)).
Lemma journal_nil_token : forall STK sp0 L A mem md L' A' mem' md',
journal ubs0_msyms MR STK sp0 [] L A mem md L' A' mem' md' ->
journal ubs0_msyms MR STK sp0 [sink_token] L A mem md L' A' mem' md'.
Proof using API.
intros STK sp0 L A mem md L' A' mem' md' (HH & Hos & Hhi & Hblk & Hgone & Hst & Herr & Himg).
assert (HE : forall a, ~ inFP [] a) by (intros a (r & [] & _)).
split; [exact HH|]. split; [eapply os_step_mono; [|exact Hos]; intros Ho; destruct (HE _ Ho)|].
split; [exact Hhi|]. split; [intros a n i H1 H2 Hi _; exact (Hblk a n i H1 H2 Hi (HE _))|].
split; [intros a n i H1 H2 Hi; destruct (HE _ (Hgone a n i H1 H2 Hi))|].
split; [exact Hst|]. split; [exact Herr|]. eapply img_kept_mono; [|exact Himg]. intros Ho. destruct (HE _ Ho).
Qed.
Lemma nil_sink_none : forall STK sp0 L A mem md L' A' mem' md',
journal ubs0_msyms MR STK sp0 [] L A mem md L' A' mem' md' -> sink_none ubs0_msyms mem md -> sink_none ubs0_msyms mem' md'.
Proof using API. intros STK sp0 L A mem md L' A' mem' md' HJ HSN. eapply (sink_none_kept ubs0_msyms MR); [exact HJ | intros (r & [] & _) | exact HSN]. Qed.
Lemma nil_fs : forall STK sp0 L A mem md L' A' mem' md',
journal ubs0_msyms MR STK sp0 [] L A mem md L' A' mem' md' -> m_fs md' = m_fs md.
Proof using API. intros STK sp0 L A mem md L' A' mem' md' (_ & Hos & _). exact (proj1 (proj2 (os_step_shielded _ _ _ Hos ltac:(intros (r & [] & _))))). Qed.
Lemma payload_kept : forall STK sp0 FP L A mem md L' A' mem' md' p PAYLOAD,
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' ->
In (p, Z.of_nat (length PAYLOAD)) (blocks L A) -> In (p, Z.of_nat (length PAYLOAD)) (blocks L' A') ->
(forall a, inFP FP a -> a < 4096) ->
garr8 ubs0segs mem p PAYLOAD -> garr8 ubs0segs mem' p PAYLOAD.
Proof using LAWS.
intros STK sp0 FP L A mem md L' A' mem' md' p PAYLOAD HJ Hin Hin' HFP HG.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH'. pose proof HJ as (_ & _ & _ & Hblk & _).
destruct (blocks_range _ _ LAWS L' A' mem' md' p _ HH' Hin') as [Hp0 _].
eapply garr8_frame; [exact HG|]. intros a Ha. replace a with (p + (a - p)) by lia.
apply (Hblk p _ (a - p) Hin Hin'); [lia|]. intros Hf. pose proof (HFP _ Hf). lia.
Qed.
Lemma inFP_token : forall a, inFP [sink_token] a -> a < 4096.
Proof using. intros a (r & [<-|[]] & Hr). cbn in Hr. lia. Qed.
Lemma inFP_nil : forall a, inFP [] a -> a < 4096.
Proof using. intros a (r & [] & _). Qed.
Lemma tmp_blocks_fp : forall L A Lc Ac memc mdc (X rest : list (Z * Z)),
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (X ++ rest) ->
(forall b, In b (blocks L A) -> In b rest) ->
forall a, inFP (blocks_fp X) a ->
exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n.
Proof using LAWS.
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
cgif_at m g s -> (forall a, 0 <= a < alloc_ceiling -> mbyte ubs0segs m' a = mbyte ubs0segs m a) -> cgif_at m' g s.
Proof using LAWS.
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
{ unfold cgif_blocks. right. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin|]. left. reflexivity. }
destruct (R (fr_ptr f) FRAME_SIZE Hfb) as [R1 R2]. unfold FRAME_SIZE in R2.
eapply obj_at_transport_range; [exact (Hf f Hin) | exact (proj1 LAY_Frame_ok) |]. intros i Hi. unfold FRAME_SIZE in Hi. apply Hlow. lia.
Qed.
Lemma cgif_at_kept : forall m m' g s N (bl rest : list (Z * Z)),
Permutation bl (cgif_blocks g s N ++ rest) ->
cgif_at m g s -> (forall b n i, In (b, n) bl -> 0 <= i < n -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m (b + i)) ->
cgif_at m' g s.
Proof using.
intros m m' g s N bl rest HB (Hg & Hr & Hf) Hkeep.
assert (K : forall b n, In (b, n) (cgif_blocks g s N) -> forall i, 0 <= i < n -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m (b + i)).
{ intros b n Hin i Hi. apply (Hkeep b n i); [|exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hin. }
unfold cgif_blocks in K.
split; [|split].
- eapply obj_at_transport_range; [exact Hg | exact (proj1 LAY_CGIF_ok) |]. apply (K g CGIF_SIZE). left. reflexivity.
- eapply obj_at_transport_range; [exact Hr | exact (proj1 LAY_Raw_ok) |]. apply (K (cg_raw s) RAW_SIZE). right. left. reflexivity.
- intros f Hin. eapply obj_at_transport_range; [exact (Hf f Hin) | exact (proj1 LAY_Frame_ok) |]. apply (K (fr_ptr f) FRAME_SIZE).
right. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
Qed.
Lemma cgif_ghost_blocks : forall g s N,
In (cg_file s, FILE_BLOCK) (cgif_blocks g s N) /\
(Z.land (cg_attr s) 4 = 0 -> In (cg_pal s, 3 * cg_ngp s) (cgif_blocks g s N)) /\
(forall f, In (Some f) (cg_frames s) ->
In (fr_img f, N) (cgif_blocks g s N) /\ (Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) (cgif_blocks g s N))).
Proof using.
intros g s N. unfold cgif_blocks, pal_blocks, frames_blocks. split; [right; right; left; reflexivity|]. split.
- intros Hz. rewrite (proj2 (Z.eqb_eq _ _) Hz). right. right. right. left. reflexivity.
- intros f Hin.
assert (HF : forall b, In b (frame_blocks N f) ->
In b ((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) :: (if Z.land (cg_attr s) 4 =? 0 then [(cg_pal s, 3 * cg_ngp s)] else []) ++
flat_map (fun o => match o with Some f0 => frame_blocks N f0 | None => [] end) (cg_frames s))).
{ intros b Hb. right. right. right. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin | exact Hb]. }
unfold frame_blocks in HF. split; [apply HF; right; left; reflexivity|].
intros Ha. apply HF. right. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
Lemma nth_frames_In : forall i (fs : list (option frame_st)) f, nth i fs None = Some f -> In (Some f) fs.
Proof using.
intros i fs f E. destruct (Nat.lt_ge_cases i (length fs)) as [Hl|Hl].
- rewrite <- E. apply nth_In. exact Hl.
- rewrite (nth_overflow fs None Hl) in E. discriminate E.
Qed.
Lemma cgif_rel_low : forall m m' mdl g s N GPAL gs Lc Ac memc mdc rest,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (cgif_blocks g s N ++ rest) ->
cgif_rel m mdl s N GPAL gs -> (forall a, 0 <= a < alloc_ceiling -> mbyte ubs0segs m' a = mbyte ubs0segs m a) ->
cgif_rel m' mdl s N GPAL gs.
Proof using LAWS.
intros m m' mdl g s N GPAL gs Lc Ac memc mdc rest HH HB (Hcur & Hsk & Hlive) Hlow.
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (cgif_ghost_blocks g s N) as (Bf & Bp & Bq).
assert (R : forall b n, In (b, n) (cgif_blocks g s N) -> 4096 <= b /\ b + n <= alloc_ceiling).
{ intros b n Hin. eapply (blocks_range _ _ LAWS); [exact HH|]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hin. }
split; [exact Hcur|]. split.
{ apply (sink_at_frame ubs0_msyms m m'); [|exact Hsk]. intros a [Ha|Ha].
- destruct (R _ _ Bf) as [R1 R2]. apply Hlow. lia.
- pose proof (ubs0_env_addr_range a Ha). apply Hlow. lia. }
intros HL. destruct (Hlive HL) as (Hrc & Hrat & Hih & Hgp & Hq0 & Hq1 & Hq2).
split; [exact Hrc|]. split; [exact Hrat|]. split; [exact Hih|]. split.
{ intros Hz. destruct (Hgp Hz) as [HG HGl]. split; [|exact HGl]. destruct (R _ _ (Bp Hz)) as [R1 R2].
eapply garr8_frame; [exact HG|]. intros a Ha. apply Hlow. lia. }
assert (FR : forall wg i q, oframe_relb wg m N (nth i (cg_frames s) None) q -> oframe_relb wg m' N (nth i (cg_frames s) None) q).
{ intros wg i q Ho. destruct (nth i (cg_frames s) None) as [f|] eqn:En; destruct q as [fr|]; cbn [oframe_relb] in Ho |- *; try exact Ho.
destruct (Bq f (nth_frames_In i _ f En)) as [Bi Bl].
destruct Ho as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & HI & HIl & HP).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [| split; [exact HIl|]].
- destruct (R _ _ Bi) as [R1 R2]. eapply garr8_frame; [exact HI|]. intros a Ha. apply Hlow. lia.
- intros Hl1. destruct (HP Hl1) as [HLP HLPl]. split; [|exact HLPl]. destruct (R _ _ (Bl Hl1)) as [R1 R2].
eapply garr8_frame; [exact HLP|]. intros a Ha. apply Hlow. lia. }
split; [apply FR; exact Hq0|]. split; [apply FR; exact Hq1|]. apply FR; exact Hq2.
Qed.
Lemma cgif_rel_kept : forall m m' mdl mdl' g s N GPAL gs STK sp0 FP L A L' A' (bl rest : list (Z * Z)),
journal ubs0_msyms MR STK sp0 FP L A m mdl L' A' m' mdl' -> ~ sink_open_fp FP ->
In (cg_file s, FILE_BLOCK) (blocks L A) -> fp_avoids FP (cg_file s) (cg_file s + FILE_BLOCK) ->
Permutation bl (cgif_blocks g s N ++ rest) ->
(forall b n i, In (b, n) bl -> 0 <= i < n -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m (b + i)) ->
cgif_rel m mdl s N GPAL gs -> cgif_rel m' mdl' s N GPAL gs.
Proof using API.
intros m m' mdl mdl' g s N GPAL gs STK sp0 FP L A L' A' bl rest HJ Hn Hfin Hav HB Hkeep (Hcur & Hsk & Hlive).
pose proof (cgif_ghost_blocks g s N) as (Bf & Bp & Bq).
assert (K : forall b n, In (b, n) (cgif_blocks g s N) -> forall l, garr8 ubs0segs m b l -> Z.of_nat (length l) = n -> garr8 ubs0segs m' b l).
{ intros b n Hin l Hl Hlen. eapply garr8_frame; [exact Hl|]. intros a Ha. replace a with (b + (a - b)) by lia.
apply (Hkeep b n (a - b)); [|lia]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hin. }
split; [exact Hcur|]. split; [exact (proj1 (sink_kept ubs0_msyms MR STK sp0 FP L A m mdl L' A' m' mdl' (cg_file s) _ HJ Hn Hfin Hav Hsk))|].
intros HL. destruct (Hlive HL) as (Hrc & Hrat & Hih & Hgp & Hq0 & Hq1 & Hq2).
split; [exact Hrc|]. split; [exact Hrat|]. split; [exact Hih|]. split.
{ intros Hz. destruct (Hgp Hz) as [HG HGl]. split; [|exact HGl]. apply (K _ _ (Bp Hz)); [exact HG | exact HGl]. }
assert (FR : forall wg i q, oframe_relb wg m N (nth i (cg_frames s) None) q -> oframe_relb wg m' N (nth i (cg_frames s) None) q).
{ intros wg i q Ho. destruct (nth i (cg_frames s) None) as [f|] eqn:En; destruct q as [fr|]; cbn [oframe_relb] in Ho |- *; try exact Ho.
destruct (Bq f (nth_frames_In i _ f En)) as [Bi Bl].
destruct Ho as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & HI & HIl & HP).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [| split; [exact HIl|]].
- apply (K _ _ Bi); [exact HI | exact HIl].
- intros Hl1. destruct (HP Hl1) as [HLP HLPl]. split; [|exact HLPl]. apply (K _ _ (Bl Hl1)); [exact HLP | exact HLPl]. }
split; [apply FR; exact Hq0|]. split; [apply FR; exact Hq1|]. apply FR; exact Hq2.
Qed.
Lemma cgif_rel_resink : forall m m' mdl mdl' g s N GPAL gs (bl rest : list (Z * Z)),
Permutation bl (cgif_blocks g s N ++ rest) ->
(forall b n i, In (b, n) bl -> 0 <= i < n -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m (b + i)) ->
cgif_rel m mdl s N GPAL gs -> sink_at ubs0_msyms m' mdl' (cg_file s) (concat (YO07.s_out gs)) ->
cgif_rel m' mdl' s N GPAL gs.
Proof using.
intros m m' mdl mdl' g s N GPAL gs bl rest HB Hkeep (Hcur & Hsk & Hlive) HSK'.
pose proof (cgif_ghost_blocks g s N) as (Bf & Bp & Bq).
assert (K : forall b n, In (b, n) (cgif_blocks g s N) -> forall l, garr8 ubs0segs m b l -> Z.of_nat (length l) = n -> garr8 ubs0segs m' b l).
{ intros b n Hin l Hl Hlen. eapply garr8_frame; [exact Hl|]. intros a Ha. replace a with (b + (a - b)) by lia.
apply (Hkeep b n (a - b)); [|lia]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hin. }
split; [exact Hcur|]. split; [exact HSK'|].
intros HL. destruct (Hlive HL) as (Hrc & Hrat & Hih & Hgp & Hq0 & Hq1 & Hq2).
split; [exact Hrc|]. split; [exact Hrat|]. split; [exact Hih|]. split.
{ intros Hz. destruct (Hgp Hz) as [HG HGl]. split; [|exact HGl]. apply (K _ _ (Bp Hz)); [exact HG | exact HGl]. }
assert (FR : forall wg i q, oframe_relb wg m N (nth i (cg_frames s) None) q -> oframe_relb wg m' N (nth i (cg_frames s) None) q).
{ intros wg i q Ho. destruct (nth i (cg_frames s) None) as [f|] eqn:En; destruct q as [fr|]; cbn [oframe_relb] in Ho |- *; try exact Ho.
destruct (Bq f (nth_frames_In i _ f En)) as [Bi Bl].
destruct Ho as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & HI & HIl & HP).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [| split; [exact HIl|]].
- apply (K _ _ Bi); [exact HI | exact HIl].
- intros Hl1. destruct (HP Hl1) as [HLP HLPl]. split; [|exact HLPl]. apply (K _ _ (Bl Hl1)); [exact HLP | exact HLPl]. }
split; [apply FR; exact Hq0|]. split; [apply FR; exact Hq1|]. apply FR; exact Hq2.
Qed.
Lemma jfree_tmp_sink :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
In (a, n) (blocks Lc Ac) -> (In (a, n) (blocks L A) -> forall i, 0 <= i < n -> False) ->
In (f, FILE_BLOCK) (blocks Lc Ac) -> (a + n <= f \/ f + FILE_BLOCK <= a) ->
sink_at ubs0_msyms (ms_mem ms) mdc f S ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S HS Hpc Hrv HJ Hid Hin Hnew Hfin Hsep HSK H10 H2 Hspc Hal Hlo Hhi H4 H1 Hraw.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [(a, a + n)] HJ) as HJl.
destruct (blocks_range _ _ LAWS Lc Ac (ms_mem ms) mdc a n (proj1 HJ) Hin) as [Ha0 Ha1].
eapply SR_mono.
{ eapply (jfree_at _ _ LAWS ubs0_errno_low IMG (aa_free API)) with (a := a) (n := n) (spc := spc);
[ exact HS | exact Hpc | exact Hrv | exact HJl | exact Hin | exact H10 | exact H2 | exact Hspc | exact Hal | exact Hlo | exact Hhi | exact H4 | exact H1 | exact Hraw | ].
intros _ i Hi. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2).
assert (HK : sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJ2 | | exact Hfin | | exact HSK].
- intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
- intros x Hx (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ | exact HJ2 | lia | lia |].
intros x (r & [<- | []] & Hr). cbn [fst snd] in Hr. right. exists a, n. split; [exact Hin|]. split; [|lia].
intros H0. exact (Hnew H0 (x - a) ltac:(lia)). }
split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hrm|]. split; [exact Hkeep|]. split; [exact Hhi2 | exact HK].
Qed.
Lemma jfree_tmp_tok :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
In (a, n) (blocks Lc Ac) -> (In (a, n) (blocks L A) -> forall i, 0 <= i < n -> False) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal ubs0_msyms MR STK sp0 [(a, a + n)] Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x))).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw HS Hpc Hrv HJ Hid Hin Hnew H10 H2 Hspc Hal Hlo Hhi H4 H1 Hraw.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [(a, a + n)] HJ) as HJl.
destruct (blocks_range _ _ LAWS Lc Ac (ms_mem ms) mdc a n (proj1 HJ) Hin) as [Ha0 Ha1].
eapply SR_mono.
{ eapply (jfree_at _ _ LAWS ubs0_errno_low IMG (aa_free API)) with (a := a) (n := n) (spc := spc);
[ exact HS | exact Hpc | exact Hrv | exact HJl | exact Hin | exact H10 | exact H2 | exact Hspc | exact Hal | exact Hlo | exact Hhi | exact H4 | exact H1 | exact Hraw | ].
intros _ i Hi. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ | exact HJ2 | lia | lia |].
intros x (r & [<- | []] & Hr). cbn [fst snd] in Hr. right. exists a, n. split; [exact Hin|]. split; [|lia].
intros H0. exact (Hnew H0 (x - a) ltac:(lia)). }
split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hrm|]. split; [exact Hkeep | exact Hhi2].
Qed.
Lemma blk_sink_none : forall STK sp0 L A mem md L' A' mem' md' a b,
journal ubs0_msyms MR STK sp0 [(a, b)] L A mem md L' A' mem' md' -> 4096 <= a ->
(sink_none ubs0_msyms mem md -> sink_none ubs0_msyms mem' md') /\ m_fs md' = m_fs md /\ m_fds md' = m_fds md.
Proof using API.
intros STK sp0 L A mem md L' A' mem' md' a b HJ Ha.
assert (Hn : ~ sink_open_fp [(a, b)]) by (intros (r & [<- | []] & Hr); cbn [fst snd] in Hr; lia).
split; [intros HSN; eapply (sink_none_kept ubs0_msyms MR); [exact HJ | exact Hn | exact HSN]|].
pose proof HJ as (_ & Hos & _). destruct (os_step_shielded _ _ _ Hos Hn) as (Efd & Efs & _). split; [exact Efs | exact Efd].
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
