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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03 UI1e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RFC_FRAME : Z := 48.
Definition RFC_DEPTH : Z := RFC_FRAME + ALLOC_STACK.
Definition RFC : Z := ubs2_A_read_frameconfig.
Definition IMGPC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x1e4).
Definition FREESPC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x234).
Definition ORPC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x228).
Definition RA_IMC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x21c).
Definition PALPC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x190).
Definition RA_PMC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x1d0).
Definition OR1PC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x1dc).
Definition EPIPC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x248).
Definition RA_FREE2 : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x244).
Lemma st_chunk_word : forall E ss ms i rg p off e a v,
st_ok ubs2segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal 8 e)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
word_mem ubs2segs (ms_mem ms) (a + off) v.
Proof.
intros E ss ms i rg p off e a v HS Hi Hb Hin Hp He Hv.
apply val_mem_word_mem.
pose proof (mem_ok_region ubs2segs E (ms_mem ms) (ss_mem ss) rg (st_ok_mem_ok ubs2segs E ss ms HS) ltac:(eapply nth_error_In; exact Hi)) as HR.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
exact (val_of_chunk_ok ubs2segs E (ms_mem ms) a off 8%N e v Hc He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma mbyte_of_frame : forall E rs (m m' : word -> option byte) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
(forall r, In r rs -> ~ (base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r)) ->
mbyte ubs2segs m' a = mbyte ubs2segs m a.
Proof.
intros E rs m m' a HF Ha Hout. unfold mbyte. rewrite HF; [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). exact (Hout r Hin Hr).
Qed.
Lemma mbyte_of_out : forall (m m' : word -> option byte) d n a,
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> m' x = m x) ->
0 <= a < 2 ^ 64 -> (a < d \/ d + n <= a) ->
mbyte ubs2segs m' a = mbyte ubs2segs m a.
Proof. intros m m' d n a H Ha Hout. unfold mbyte. rewrite H; [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hout. Qed.

Lemma word_mem_frame : forall (m m' : word -> option byte) a v,
word_mem ubs2segs m a v -> (forall i, 0 <= i < 8 -> mbyte ubs2segs m' (a + i) = mbyte ubs2segs m (a + i)) ->
word_mem ubs2segs m' a v.
Proof. intros m m' a v H Hf k Hk. rewrite Hf by lia. apply H. exact Hk. Qed.
Lemma regs_preserved_intro : forall regs regs' : bvmap 5 word,
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
End b.
Ltac mb_frame HF :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
rewrite (mbyte_of_frame E rs m m' _ HF); [ | lia |
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; repeat (rewrite ew_havoc_old; [|cbv; lia]) |]);
[ .. | destruct Hr ] ]
end.
Ltac wr3_tac HE2 HE8 HE18 :=
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE8 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE18 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil.
Ltac reg_final HS HX HE HE2 rr :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q := fresh "Q" in
pose proof (st_ok_reg ubs2segs Ef ssf msf rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
repeat (rewrite ew_havoc_old in Q; [|cbv; lia]); rewrite ?Z.add_0_r in Q;
cbn [ms_regs mkst]; rewrite Q; clear Q;
first [ rewrite Z_to_bv_bv_unsigned;
first [ rewrite (HX 32%nat 0%nat _ eq_refl eq_refl) | rewrite (HX 33%nat 1%nat _ eq_refl eq_refl) | rewrite (HX 34%nat 2%nat _ eq_refl eq_refl)
| rewrite (HX 35%nat 3%nat _ eq_refl eq_refl) | rewrite (HX 36%nat 4%nat _ eq_refl eq_refl) | rewrite (HX 37%nat 5%nat _ eq_refl eq_refl)
| rewrite (HX 38%nat 6%nat _ eq_refl eq_refl) | rewrite (HX 39%nat 7%nat _ eq_refl eq_refl) | rewrite (HX 40%nat 8%nat _ eq_refl eq_refl)
| rewrite (HE 3%nat 3%bv eq_refl) | rewrite (HE 4%nat 4%bv eq_refl)
| rewrite (HE 21%nat 21%bv eq_refl) | rewrite (HE 22%nat 22%bv eq_refl) | rewrite (HE 23%nat 23%bv eq_refl) | rewrite (HE 24%nat 24%bv eq_refl)
| rewrite (HE 25%nat 25%bv eq_refl) | rewrite (HE 26%nat 26%bv eq_refl) | rewrite (HE 27%nat 27%bv eq_refl) ];
first [ reflexivity | assumption | symmetry; assumption ]
| rewrite HE2; unfold RFC_FRAME;
match goal with |- Z_to_bv 64 ?x = getr ?rg0 _ => replace x with (spZ rg0) by lia end;
unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
| idtac ]
end.
Ltac rfc_img_post HS HJ Hid HX HE HE2 G3 G4 G24 G25 G26 G27 Hra0 res cur2 img :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in let Q10 := fresh "Q10" in
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|cbv; lia]); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q1;
rewrite (HX 32%nat 0%nat _ eq_refl eq_refl) in Q1;
lazymatch goal with |- ?hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdl) =>
eexists _, _, rg, mm, mdl end;
exists res, cur2, img;
split; [ cbn [ms_regs mkst]; rewrite Q1, Hra0; reflexivity |];
split; [ exact HJ |];
split; [ exact Hid |];
split; [ apply regs_preserved_intro;
[ reg_final HS HX HE HE2 (2%bv:reg) | reg_final HS HX HE HE2 (3%bv:reg) | reg_final HS HX HE HE2 (4%bv:reg) | reg_final HS HX HE HE2 (8%bv:reg)
| reg_final HS HX HE HE2 (9%bv:reg) | reg_final HS HX HE HE2 (18%bv:reg) | reg_final HS HX HE HE2 (19%bv:reg) | reg_final HS HX HE HE2 (20%bv:reg)
| reg_final HS HX HE HE2 (21%bv:reg) | reg_final HS HX HE HE2 (22%bv:reg) | reg_final HS HX HE HE2 (23%bv:reg) | reg_final HS HX HE HE2 (24%bv:reg)
| reg_final HS HX HE HE2 (25%bv:reg) | reg_final HS HX HE HE2 (26%bv:reg) | reg_final HS HX HE HE2 (27%bv:reg) ] |];
split; [ pose proof (st_ok_reg ubs2segs Ef ssf msf 10%bv HS) as Q10; eval_sr_get_in Q10; cbn [sv_denot] in Q10; cbn [ms_regs mkst]; rewrite Q10; reflexivity |];
split; [| split; [| split ]]
end.
Ltac frame_word HS HX HE2 off j d :=
lazymatch goal with |- word_mem _ (ms_mem ?msc) (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with ((spv - RFC_FRAME) + off) by (unfold RFC_FRAME; lia);
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat off (SOff (32 + j) 0) (spv - RFC_FRAME) (bv_unsigned w) HS);
[ reflexivity | reflexivity | cbv; auto 12
| repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HE2
| cbn [sv_denot]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite Z.add_0_r, (HX (32 + j)%nat j w eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; lia ]
end.
Ltac pal_post_tac HS HJ Hid HX HE HE2 G3 G4 G24 G25 G26 G27 Hra0 res cur2 img lp lpb :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|cbv; lia]); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q1;
rewrite (HX 32%nat 0%nat _ eq_refl eq_refl) in Q1;
lazymatch goal with |- ?hd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdl) =>
eexists _, _, rg, mm, mdl end;
exists res, cur2, img, lp, lpb;
split; [ cbn [ms_regs mkst]; rewrite Q1, Hra0; reflexivity |];
split; [ exact HJ |];
split; [ exact Hid |];
split; [ apply regs_preserved_intro;
[ reg_final HS HX HE HE2 (2%bv:reg) | reg_final HS HX HE HE2 (3%bv:reg) | reg_final HS HX HE HE2 (4%bv:reg) | reg_final HS HX HE HE2 (8%bv:reg)
| reg_final HS HX HE HE2 (9%bv:reg) | reg_final HS HX HE HE2 (18%bv:reg) | reg_final HS HX HE HE2 (19%bv:reg) | reg_final HS HX HE HE2 (20%bv:reg)
| reg_final HS HX HE HE2 (21%bv:reg) | reg_final HS HX HE HE2 (22%bv:reg) | reg_final HS HX HE HE2 (23%bv:reg) | reg_final HS HX HE HE2 (24%bv:reg)
| reg_final HS HX HE HE2 (25%bv:reg) | reg_final HS HX HE HE2 (26%bv:reg) | reg_final HS HX HE HE2 (27%bv:reg) ] |];
split; [ pose proof (st_ok_reg ubs2segs Ef ssf msf 10%bv HS) as Q10; eval_sr_get_in Q10; cbn [sv_denot] in Q10; cbn [ms_regs mkst]; rewrite Q10; reflexivity |];
split; [| split; [| split ]]
end.
Ltac reg_now HS tac :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch goal with |- getr _ ?rr = _ =>
let T := fresh "T" in
pose proof (st_ok_reg ubs2segs Ec ssc msc rr HS) as T; eval_sr_get_in T; cbn [sv_denot] in T;
repeat (rewrite ew_havoc_old in T; [|cbv; lia]); rewrite ?Z.add_0_r in T;
cbn [ms_regs mkst]; rewrite T; clear T; tac
end
end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition hideP (P : Prop) : Prop := P.
Lemma hideP_i : forall P : Prop, P -> hideP P. Proof. intros P H; exact H. Qed.
End c.
Ltac nat_lt_lit := apply (proj1 (Nat.ltb_lt _ _)); reflexivity.
Ltac ew_havocF := repeat (rewrite ew_havoc_old; [|nat_lt_lit]).
Ltac mb_frame_with HF rng win :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
rewrite (mbyte_of_frame E rs m m' _ HF); [ | rng |
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havocF; win |]);
[ .. | destruct Hr ] ]
end.
Ltac mbfA HF Ha Hn1 Hn2 Hn3 Hac HFRv HDPv HASv HE2 HE8 HE18 :=
mb_frame_with HF ltac:(clear - Ha Hac; lia)
ltac:(rewrite ?HE2, ?HE8, ?HE18;
first [ solve [clear - Ha Hn1 HFRv HDPv HASv; lia] | solve [clear - Ha Hn2; lia] | solve [clear - Ha Hn3; lia]
| idtac "mbfA: slow fallback"; lia ]).
Ltac mbfB HF Hb0 Hb1 Hi Hac Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv HE2 HE8 HE18 :=
mb_frame_with HF ltac:(clear - Hb0 Hb1 Hi Hac; lia)
ltac:(rewrite ?HE2, ?HE8, ?HE18;
first [ solve [clear - Hb1 Hi Hceil Hwlo Hst1 Hdst1 HFRv HDPv HASv Hac; lia]
| idtac "mbfB: slow fallback"; lia ]).
Ltac wr3_tac_with HE2 HE8 HE18 slv :=
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE2 | cbn [r_wlo r_whi]; intros _; slv |];
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE8 | cbn [r_wlo r_whi]; intros _; slv |];
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HE18 | cbn [r_wlo r_whi]; intros _; slv |];
apply wr_ok_nil.
Ltac frame_wordF HS HX HE2 off j d :=
lazymatch goal with |- word_mem _ (ms_mem ?msc) (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with ((spv - RFC_FRAME) + off) by (unfold RFC_FRAME; ring);
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat off (SOff (32 + j) 0) (spv - RFC_FRAME) (bv_unsigned w) HS);
[ reflexivity | reflexivity | cbv; auto 12
| ew_havocF; exact HE2
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HX (32 + j)%nat j w eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity
| let Rw := fresh "Rw" in pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; clear - Rw; lia ]
end.
Ltac reg_nowF HS tac :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch goal with |- getr _ ?rr = _ =>
let T := fresh "T" in
pose proof (st_ok_reg ubs2segs Ec ssc msc rr HS) as T; eval_sr_get_in T; cbn [sv_denot] in T;
repeat (rewrite ew_havoc_old in T; [|nat_lt_lit]); rewrite ?Z.add_0_r in T;
cbn [ms_regs mkst]; rewrite T; clear T; tac
end
end.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma fresh_not_in : forall L A mem md b1 b2 a n,
heap_ok MR L A mem md -> blocks L A = b1 ++ (a, n) :: b2 -> 0 < n -> ~ In (a, n) (b1 ++ b2).
Proof.
intros L A mem md b1 b2 a n HH HB Hn Hin.
pose proof (heap_sep _ _ LAWS L A mem md b1 (a, n) b2 (a, n) HH HB Hin) as H. cbn [fst snd] in H. lia.
Qed.
End S.
End f.
