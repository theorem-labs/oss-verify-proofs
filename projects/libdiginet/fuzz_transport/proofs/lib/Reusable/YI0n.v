(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI0n.v, with its module paths changed. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/YI0n.v at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI04 YI08 YI0t YI0m.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition nz (l : list (Z * Z)) : list (Z * Z) := List.filter (fun b => negb (fst b =? 0)) l.
Lemma nz_cons0 : forall n l, nz ((0, n) :: l) = nz l.
Proof. intros n l. reflexivity. Qed.
Lemma nz_cons_nz : forall p n l, p <> 0 -> nz ((p, n) :: l) = (p, n) :: nz l.
Proof. intros p n l Hp. unfold nz. cbn. destruct (Z.eqb_spec p 0); [lia | reflexivity]. Qed.
Lemma In_nz : forall b l, In b (nz l) <-> In b l /\ fst b <> 0.
Proof.
intros b l. unfold nz. split; [intros H; apply filter_In in H as [H1 H2] | intros [H1 H2]; apply filter_In]; split; auto.
- destruct (Z.eqb_spec (fst b) 0); [discriminate | assumption].
- destruct (Z.eqb_spec (fst b) 0); [lia | reflexivity].
Qed.
Lemma regs_preserved_intro_lzw : forall regs regs' : bvmap 5 word,
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
regs_preserved regs regs'.
Proof.
intros regs regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
unfold callee_saved in Hr.
assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hcases as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; assumption.
Qed.
Lemma st_ok_pin_reg' : forall segs E ss ms (r : reg) z,
st_ok segs E ss ms -> getr (ms_regs ms) r = Z_to_bv 64 z -> bv_eqb r 0 = false ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms r z HS Hr Hr0. apply st_ok_regs; [exact HS|].
intros rr. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. cbn [sv_denot]. rewrite <- (st_ok_reg segs E ss ms r HS), Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
End g.
Ltac pin_reg' HS r z Hval :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
let H2 := fresh "HSp" in
pose proof (st_ok_pin_reg' segs E1 ss1 ms1 r z HS ltac:(first [exact Hval | cbn [ms_regs]; exact Hval | cbn [ms_regs]; rewrite Hval; reflexivity]) eq_refl) as H2;
let v := eval vm_compute in (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) r (SLit z)) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) in
change (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) r (SLit z)) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) with v in H2;
clear HS; rename H2 into HS
end.
Ltac add_fact' HS n f :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_fact segs E1 ss1 ms1 n f) in HS;
[ let v := eval vm_compute in (add_atom ss1 n f) in change (add_atom ss1 n f) with v in HS
| unfold afact_ok; cbn [af_lo af_hi af_al2] ]
end.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_add_region' : forall segs E ss ms r,
st_ok segs E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrwf Hr Hd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [cbn; rewrite Hrwf, Hwf; reflexivity|]. split; [constructor; assumption|]. split; assumption.
Qed.
Lemma disj_of_pointwise : forall a n b m,
(forall i, 0 <= i < n -> ~ (b <= a + i < b + m)) -> 0 < n -> 0 < m -> a + n <= b \/ b + m <= a.
Proof.
intros a n b m H Hn Hm.
destruct (Z_lt_le_dec b (a + n)) as [H1|H1]; [|left; lia].
destruct (Z_lt_le_dec a (b + m)) as [H2|H2]; [|right; lia].
exfalso. destruct (Z_lt_le_dec a b) as [H3|H3].
- apply (H (b - a)); lia.
- apply (H 0); lia.
Qed.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Local Notation segs := (ms_segs B) (only parsing).
Definition ftok (FP : list (Z * Z)) (bl0 : list (Z * Z)) (b : Z * Z) : Prop :=
In b bl0 -> forall i, 0 <= i < snd b -> inFP FP (fst b + i).
Definition wtok' (STK sp0 : Z) (FP bl0 : list (Z * Z)) (b : Z * Z) : Prop :=
forall blc i, In b blc -> 0 <= i < snd b -> wr_byte STK sp0 FP bl0 blc (fst b + i).
Lemma ftok_of_wtok : forall STK sp0 FP bl0 p n,
wtok' STK sp0 FP bl0 (p, n) -> p + n <= alloc_ceiling -> alloc_ceiling + STK <= sp0 ->
ftok FP bl0 (p, n).
Proof.
intros STK sp0 FP bl0 p n HW Hpn Hsp Hin i Hi. cbn [fst snd] in *.
destruct (HW [(p, n)] i ltac:(left; reflexivity) Hi) as [Hs | [[Hf _] | (b & m & Hb & Hnb & _)]]; cbn [fst snd] in *.
- exfalso. lia.
- exact Hf.
- exfalso. destruct Hb as [Hb | []]. inversion Hb; subst. exact (Hnb Hin).
Qed.
Lemma wr_byte_of_wtok : forall STK sp0 FP bl0 blc p n a,
wtok' STK sp0 FP bl0 (p, n) -> In (p, n) blc -> p <= a < p + n -> wr_byte STK sp0 FP bl0 blc a.
Proof.
intros STK sp0 FP bl0 blc p n a HW Hin Ha. replace a with (p + (a - p)) by lia.
apply (HW blc (a - p) Hin). cbn [snd]. lia.
Qed.
Lemma jfree_tok : free_realizes B MR -> free_null_realizes B ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
(a = 0 \/ (In (a, n) (blocks Lc Ac) /\ ftok FP (blocks L A) (a, n))) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
(a = 0 /\ blocks L2 A2 = blocks Lc Ac \/ a <> 0 /\ rm1 (a, n) (blocks Lc Ac) (blocks L2 A2)) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HFR HFN E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw
HS Hpc Hrv HJ Hid Ha Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
destruct (Z.eq_dec a 0) as [Hz | Hnz].
- subst a. destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono; [eapply (jfree_null B HFN); try eassumption|].
intros c' ->. exists Lc, Ac, (ms_regs ms), (ms_mem ms), mdc.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hid|]. split; [intros r Hr; reflexivity|].
split; [left; split; reflexivity|]. split; [intros; reflexivity|]. intros x _ _. split; [reflexivity | tauto].
- destruct Ha as [Hz | [Hin Htok]]; [lia|].
eapply SR_mono; [eapply (jfree_at B MR LAWS errno_low IMG HFR); try eassumption; exact Htok|].
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|].
split; [right; split; [exact Hnz | exact Hrm]|]. split; [exact Hkeep | exact Hhi2].
Qed.
Lemma journal_restart : forall STK sp0 FP L A mem md Lc Ac memc mdc FP',
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
journal B MR STK sp0 FP' Lc Ac memc mdc Lc Ac memc mdc.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc FP' (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
split; [exact HH|]. split; [exists (m_vmmaps mdc); apply with_vmmaps_self|].
split; [intros a Ha Hna; split; [reflexivity | tauto]|].
split; [intros; reflexivity|]. split; [intros a n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hst|]. split; [exact Herr | apply img_kept_refl].
Qed.
Lemma journal_blocks_kept : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' ->
forall a n i, In (a, n) (blocks L A) -> In (a, n) (blocks L' A') -> 0 <= i < n ->
~ inFP FP (a + i) -> mbyte segs mem' (a + i) = mbyte segs mem (a + i).
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & Hblk & _). exact Hblk. Qed.
Lemma journal_high_kept : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a).
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & Hhigh & _). exact Hhigh. Qed.
Lemma journal_img_kept : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> img_kept B mem mem'.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & _ & _ & _ & _ & Himg). exact Himg. Qed.
Lemma journal_stack_ok : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> stack_ok B STK sp0 mem'.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & _ & _ & Hst & _). exact Hst. Qed.
Definition SAVED : list (reg * Z) :=
[(1%bv, 8); (8%bv, 16); (9%bv, 24); (18%bv, 32); (19%bv, 40); (20%bv, 48); (21%bv, 56); (22%bv, 64); (23%bv, 72); (24%bv, 80); (25%bv, 88); (26%bv, 96); (27%bv, 104)].
Definition frame_saved (regs0 : bvmap 5 word) (m : word -> option byte) (spe : Z) : Prop :=
forall r d, In (r, d) SAVED -> word_mem segs m (spe - d) (bv_unsigned (getr regs0 r)).
Lemma frame_saved_kept : forall regs0 m m' spe,
frame_saved regs0 m spe ->
(forall a, spe - 104 <= a < spe -> mbyte segs m' a = mbyte segs m a) ->
frame_saved regs0 m' spe.
Proof.
intros regs0 m m' spe H Hf r d Hin k Hk.
assert (Hd : 8 <= d <= 104).
{ cbv [SAVED In] in Hin. repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; lia|]). destruct Hin. }
rewrite Hf by lia. apply (H r d Hin). exact Hk.
Qed.
Lemma frame_saved_of_region : forall E m regs0 spe cs lo hi wlo whi,
region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe ->
(forall r d, In (r, d) SAVED -> exists e, In (mkChunk (- d) (CVal 8 e)) cs /\ sv_denot E e = getr regs0 r) ->
frame_saved regs0 m spe.
Proof.
intros E m regs0 spe cs lo hi wlo whi (_ & _ & _ & Hcs) H2 Hsv r d Hrd.
destruct (Hsv r d Hrd) as (e & Hin & He).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [r_base base_val] in Hc. rewrite H2 in Hc.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
apply val_mem_word_mem. replace (spe - d) with (spe + - d) by lia.
exact (val_of_chunk_ok segs E m spe (- d) 8%N e (bv_unsigned (getr regs0 r)) Hc
ltac:(rewrite He; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Definition saved_vals (regs0 : bvmap 5 word) : list word := map (fun rd => getr regs0 (fst rd)) SAVED.
Definition saved_chunks (k : nat) : list YP09.chunk :=
map (fun jd => mkChunk (208 - snd jd) (CVal 8 (SOff (k + fst jd)%nat 0)))
(combine (seq 0 13) (map snd SAVED)).
Lemma saved_chunks_ok : forall E m regs0 spe k,
(forall j, (j < 13)%nat -> ew E (k + j)%nat = nth j (saved_vals regs0) (Z_to_bv 64 0)) ->
frame_saved regs0 m spe ->
Forall (chunk_ok segs E m (spe - 208)) (saved_chunks k).
Proof.
intros E m regs0 spe k HE HF.
unfold saved_chunks. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([j d] & <- & Hjd).
cbn [fst snd].
apply in_combine_r in Hjd as Hd0. pose proof (in_combine_l _ _ _ _ Hjd) as Hj0. apply in_seq in Hj0.
assert (Hnth : nth_error (map snd SAVED) j = Some d /\ exists r, nth_error SAVED j = Some (r, d)).
{ clear - Hjd. cbv [SAVED map snd combine seq] in Hjd.
repeat (destruct Hjd as [Hjd|Hjd]; [inversion Hjd; subst; split; [reflexivity | eexists; reflexivity] |]). destruct Hjd. }
destruct Hnth as [Hnd (r & Hr)].
assert (Hin : In (r, d) SAVED) by (eapply nth_error_In; exact Hr).
pose proof (HF r d Hin) as W.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
eapply (chunk_ok_val segs E m (spe - 208) _ 8%N _ (bv_unsigned (getr regs0 r))).
- cbn [sv_denot]. rewrite Z.add_0_r, (HE j ltac:(lia)).
unfold saved_vals. erewrite (nth_error_nth _ _ _ (map_nth_error _ _ _ Hr)). cbn [fst]. rewrite Z_to_bv_bv_unsigned. reflexivity.
- cbn. lia.
- cbn. lia.
- replace (spe - 208 + (208 - d)) with (spe - d) by lia. apply val_mem_word_mem. exact W.
Qed.
End J.
End h.
