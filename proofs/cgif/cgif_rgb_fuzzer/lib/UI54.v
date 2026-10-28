(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 UI56 YI0x YL0e YI08 YI0c UI3h
UI4y UO0e UIZe UIZf YI0d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition ro (r : YQ0b.region) : YQ0b.region := YQ0b.mkRegion (r_base r) (r_lo r) (r_hi r) 0 0 (r_chunks r).
Lemma subregion_ro_lit : forall b lo hi wlo whi cs,
subregion (YQ0b.mkRegion b lo hi 0 0 cs) (YQ0b.mkRegion b lo hi wlo whi cs).
Proof. intros b lo hi wlo whi cs. unfold subregion. cbn. repeat split; try lia. auto. Qed.
Ltac submem_ro_tac :=
repeat first [ apply submem_nil
| apply submem_keep; [apply subregion_ro_lit|]
| apply submem_drop ].
Ltac jafter_call_ro HS k regs2 mem2 HP idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (map ro (pick (ss_mem ss) idxs)) in
let retpc := eval vm_compute in (match sr_get (ss_regs ss) 1 with SLit z => z | _ => 0 end) in
pose proof (st_ok_after_call segs k E ss ms regs2 mem2 rs retpc HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_ro_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retpc) in
change (ss_after_call ss rs k retpc) with ss2 in HS2
end.
Ltac wr_img HEd :=
wr_norm; apply wr_ok_cons_ro; [cbn; lia|];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HEd | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_nil.
Ltac wr_img_ro :=
wr_norm; repeat (apply wr_ok_cons_ro; [cbn; lia|]); apply wr_ok_nil.
Ltac pin10 HS v Hq :=
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_regs ubs2segs E1 ss1 ms1 (sr_set (ss_regs ss1) 10%bv (SLit v))) in HS;
[| intros rr; destruct (decide (rr = 10%bv)) as [->|Hne];
[ rewrite sr_get_set_same by reflexivity;
match goal with |- _ = sv_denot _ ?w => let w' := eval vm_compute in w in change w with w' end;
cbn [sv_denot]; rewrite Z.add_0_r, Hq, Z_to_bv_bv_unsigned; reflexivity
| rewrite sr_get_set_other by exact Hne; reflexivity ] ] end;
lazymatch type of HS with st_ok _ _ ?ss1 _ => let w := eval vm_compute in ss1 in change ss1 with w in HS end.
Ltac rreg_final HS HX HE HE2 rr :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q := fresh "Q" in
pose proof (st_ok_reg ubs2segs Ef ssf msf rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
repeat (rewrite ew_havoc_old in Q; [|cbv; lia]); rewrite ?Z.add_0_r in Q;
cbn [ms_regs mkst]; rewrite Q; clear Q;
first [ rewrite Z_to_bv_bv_unsigned;
first [ rewrite (HX 33%nat 1%nat _ eq_refl eq_refl) | rewrite (HX 34%nat 2%nat _ eq_refl eq_refl)
| rewrite (HX 35%nat 3%nat _ eq_refl eq_refl) | rewrite (HX 36%nat 4%nat _ eq_refl eq_refl) | rewrite (HX 37%nat 5%nat _ eq_refl eq_refl)
| rewrite (HX 38%nat 6%nat _ eq_refl eq_refl) | rewrite (HX 39%nat 7%nat _ eq_refl eq_refl) | rewrite (HX 40%nat 8%nat _ eq_refl eq_refl)
| rewrite (HE 3%nat 3%bv eq_refl) | rewrite (HE 4%nat 4%bv eq_refl)
| rewrite (HE 23%nat 23%bv eq_refl) | rewrite (HE 24%nat 24%bv eq_refl)
| rewrite (HE 25%nat 25%bv eq_refl) | rewrite (HE 26%nat 26%bv eq_refl) | rewrite (HE 27%nat 27%bv eq_refl) ];
first [ reflexivity | assumption | symmetry; assumption ]
| rewrite HE2; unfold RRFC_FRAME;
match goal with |- Z_to_bv 64 ?x = getr ?rg0 _ => replace x with (spZ rg0) by lia end;
unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
| idtac ]
end.
Ltac rimg_fin HS HJ Hid HX HE HE2 Hra0 res cur2 img :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|cbv; lia]); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q1;
rewrite (HX 40%nat 8%nat _ eq_refl eq_refl) in Q1;
lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdl] =>
eexists _, _, rg, mm, mdl end;
exists res, cur2, img;
split; [ cbn [ms_regs mkst]; rewrite Q1, Hra0; reflexivity |];
split; [ exact HJ |];
split; [ exact Hid |];
split; [ apply regs_preserved_intro;
[ rreg_final HS HX HE HE2 (2%bv:reg) | rreg_final HS HX HE HE2 (3%bv:reg) | rreg_final HS HX HE HE2 (4%bv:reg) | rreg_final HS HX HE HE2 (8%bv:reg)
| rreg_final HS HX HE HE2 (9%bv:reg) | rreg_final HS HX HE HE2 (18%bv:reg) | rreg_final HS HX HE HE2 (19%bv:reg) | rreg_final HS HX HE HE2 (20%bv:reg)
| rreg_final HS HX HE HE2 (21%bv:reg) | rreg_final HS HX HE HE2 (22%bv:reg) | rreg_final HS HX HE HE2 (23%bv:reg) | rreg_final HS HX HE HE2 (24%bv:reg)
| rreg_final HS HX HE HE2 (25%bv:reg) | rreg_final HS HX HE HE2 (26%bv:reg) | rreg_final HS HX HE HE2 (27%bv:reg) ] |];
split; [ pose proof (st_ok_reg ubs2segs Ef ssf msf 10%bv HS) as Q10; eval_sr_get_in Q10; cbn [sv_denot] in Q10; cbn [ms_regs mkst]; rewrite Q10; reflexivity |];
split; [| split; [| split; [| split ]]]
end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition rimg_frame : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 0 RRFC_FRAME 0 0
[mkChunk 15 (CVal 1 (SOff 32 0)); mkChunk 16 (CVal 8 (SOff 33 0)); mkChunk 24 (CVal 8 (SOff 34 0));
mkChunk 32 (CVal 8 (SOff 35 0)); mkChunk 40 (CVal 8 (SOff 36 0)); mkChunk 48 (CVal 8 (SOff 37 0));
mkChunk 56 (CVal 8 (SOff 38 0)); mkChunk 64 (CVal 8 (SOff 39 0)); mkChunk 72 (CVal 8 (SOff 40 0))].
Definition ss_rimg (ok : bool) : sstate :=
mkSS RR_MAL
(if ok then sr_set (sr_set (sr_set (sr_set sr_atoms 19%bv (SLit 0)) 20%bv (SLit 0)) 21%bv (SLit 0)) 10%bv (SLit 0) else sr_atoms)
[ rimg_frame ; YQ0b.mkRegion (Some 8%nat) 0 12 0 (if ok then 12 else 0) [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (8%nat, mkAF CEIL_MIN (2^63) 3); (9%nat, mkAF CEIL_MIN (2^63) 3);
(18%nat, mkAF 1 RGB_NMAX 0); (32%nat, mkAF 0 255 0) ] [] []).
Lemma denot_add0_mul : forall E a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x * y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SOff b 0)) (SLit 0)) = Z_to_bv 64 (x * y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb), U_SLit by lia. change (zcanon 0) with 0.
rewrite Z.add_0_r, (zcanon_id (x * y)) by (unfold M64; nia). apply zcanon_id. unfold M64; nia.
Qed.
Lemma fmt_okb_bad_branch : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
branch_taken BC_GEU (sv_denot E (SOff n (-5))) (sv_denot E (SLit 18446744073709551614)) = fmt_okb b.
Proof.
intros E n b Hn Hb. rewrite branch_geu_U. unfold U. cbn [sv_denot]. rewrite Hn.
rewrite (unsigned_lit_small b) by lia.
rewrite Z_to_bv_unsigned. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (18446744073709551614 mod 2 ^ 64) with (2 ^ 64 - 2) by reflexivity.
unfold fmt_okb.
destruct (Z_lt_le_dec b 5) as [Hl|Hl].
- replace ((b + -5) mod 2 ^ 64) with (b + -5 + 2 ^ 64).
2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
destruct (Z.eqb_spec b 3) as [->|H3]; [reflexivity|]. destruct (Z.eqb_spec b 4) as [->|H4]; [reflexivity|].
cbn [orb]. apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
- rewrite Z.mod_small by lia.
destruct (Z.eqb_spec b 3) as [->|H3]; [lia|]. destruct (Z.eqb_spec b 4) as [->|H4]; [lia|].
cbn [orb]. apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.
Lemma fmt_okb_range : forall b, fmt_okb b = true -> b = 3 \/ b = 4.
Proof. intros b H. unfold fmt_okb in H. apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; auto. Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition rimg_post (regs0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md
(Bb : list (Z * Z)) (st dst N nb cur fb : Z) (mem1 : word -> option byte) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res cur2 img : Z),
c' = mkCfg (mkst regs2 (getr regs0 1) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs0 regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs0 - RRFC_STK <= a < spZ regs0) -> ~ (dst <= a < dst + 12) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs2segs mem2 a = mbyte ubs2segs mem1 a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs mem1 (b + i)) /\
word_mem ubs2segs mem2 (st + 16) cur2 /\
cur <= cur2 <= nb /\
((fmt_okb fb = false /\ res = 2 ^ 64 - 1 /\ Permutation (blocks L2 A2) Bb /\
(forall a, dst <= a < dst + 12 -> mbyte ubs2segs mem2 a = mbyte ubs2segs mem1 a)) \/
(fmt_okb fb = true /\ res = 0 /\ Permutation (blocks L2 A2) Bb) \/
(fmt_okb fb = true /\ res = 1 /\ word_mem ubs2segs mem2 dst img /\ 0 <= img < 2 ^ 64 /\
val_mem ubs2segs mem2 (dst + 8) 4 fb /\ Permutation (blocks L2 A2) ((img, fb * N) :: Bb))).
Lemma rfc_img :
forall STK sp0 FP L A mem md Lc Ac mdc (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte)
(Bb : list (Z * Z)) (st dst N pdata nb cur fb : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) ->
Permutation (blocks Lc Ac) Bb ->
In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
spZ regs0 mod 16 = 0 -> sp0 - STK <= spZ regs0 - RRFC_STK -> spZ regs0 <= sp0 ->
spZ regs0 <= st -> st + 24 <= sp0 -> spZ regs0 <= dst -> dst + RGBFC_SIZE <= sp0 -> (st + 24 <= dst \/ dst + RGBFC_SIZE <= st) ->
st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= RGB_NMAX -> 0 <= cur <= nb -> 0 < nb -> 0 <= fb < 256 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - RRFC_FRAME) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = Z_to_bv 64 dst -> getr regs1 9 = Z_to_bv 64 st -> getr regs1 18 = Z_to_bv 64 N ->
(fmt_okb fb = true -> getr regs1 19 = Z_to_bv 64 0 /\ getr regs1 20 = Z_to_bv 64 0 /\ getr regs1 21 = Z_to_bv 64 0 /\
getr regs1 10 = Z_to_bv 64 0) ->
getr regs1 22 = getr regs0 22 -> getr regs1 23 = getr regs0 23 -> getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 ->
getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
mbyte ubs2segs mem1 (spZ regs0 - 65) = Some (Z_to_bv 8 fb) ->
word_mem ubs2segs mem1 (spZ regs0 - 64) (bv_unsigned (getr regs0 22)) ->
word_mem ubs2segs mem1 (spZ regs0 - 56) (bv_unsigned (getr regs0 21)) ->
word_mem ubs2segs mem1 (spZ regs0 - 48) (bv_unsigned (getr regs0 20)) ->
word_mem ubs2segs mem1 (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
word_mem ubs2segs mem1 (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem ubs2segs mem1 (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem ubs2segs mem1 (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem ubs2segs mem1 (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem ubs2segs mem1 st pdata -> word_mem ubs2segs mem1 (st + 8) nb -> word_mem ubs2segs mem1 (st + 16) cur ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 RR_MAL) mem1 (seg_rom ubs2segs)) mdc)
(rimg_post regs0 STK sp0 FP L A mem md Bb st dst N nb cur fb mem1).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs0 regs1 mem1 Bb st dst N pdata nb cur fb
HJ Hid Hbase HBc Hpd Hra0 Htp0 Hal16 Hwlo Hwhi Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Hfb
G2 G3 G4 G8 G9 G18 Gok G22 G23 G24 G25 G26 G27 Bf W22 W21 W20 W19 W18 W9 W8 W1 Wp Wn Wc.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RRFC_FRAME = 80) by reflexivity. assert (HDPv : RRFC_STK = 8272) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
assert (HRDS : RD_STK = 32) by reflexivity. assert (HRDN : RD_NMAX = 40000) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
set (sp := spZ regs0) in *.
assert (Hspm : (sp - RRFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
set (extra := [Z_to_bv 64 fb; getr regs0 22; getr regs0 21; getr regs0 20; getr regs0 19; getr regs0 18;
getr regs0 9; getr regs0 8; getr regs0 1]).
set (E := Ereg regs1 extra).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall n j v, (n = 32 + j)%nat -> nth_error extra j = Some v -> ew E n = v).
{ intros n j v -> Hj. subst E. rewrite ew_Ereg_extra. apply nth_error_nth. exact Hj. }
assert (HE2 : bv_unsigned (ew E 2) = sp - RRFC_FRAME) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HEs : bv_unsigned (ew E 9) = st) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HEd : bv_unsigned (ew E 8) = dst) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HE18 : ew E 18 = Z_to_bv 64 N) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE32 : ew E 32 = Z_to_bv 64 fb) by (apply (HX 32%nat 0%nat _ eq_refl eq_refl)).
assert (HEA : env_agree 32 (Ereg regs1 extra) E) by (subst E; split; [intros k Hk; reflexivity | reflexivity]).
assert (FRAMEOK : region_ok ubs2segs E mem1 rimg_frame).
{ unfold region_ok, rimg_frame. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
assert (CK : forall off j (w : word) (W : word_mem ubs2segs mem1 (sp - RRFC_FRAME + off) (bv_unsigned w)),
nth_error extra j = Some w ->
chunk_ok ubs2segs E mem1 (sp - RRFC_FRAME) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w W Hj. eapply (chunk_ok_val _ _ _ _ _ _ _ (bv_unsigned w));
[| pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; cbn; lia | cbn; lia | apply val_mem_word_mem; exact W].
cbn [sv_denot]. rewrite Z.add_0_r, (HX (32 + j)%nat j w eq_refl Hj), Z_to_bv_bv_unsigned. reflexivity. }
apply Forall_cons.
{ eapply (chunk_ok_val _ _ _ _ _ _ _ fb); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_byte; [|exact Hfb]. replace (sp - RRFC_FRAME + 15) with (sp - 65) by lia. exact Bf. }
apply Forall_cons. { eapply (CK 16 1%nat); [replace (sp - RRFC_FRAME + 16) with (sp - 64) by lia; exact W22 | reflexivity]. }
apply Forall_cons. { eapply (CK 24 2%nat); [replace (sp - RRFC_FRAME + 24) with (sp - 56) by lia; exact W21 | reflexivity]. }
apply Forall_cons. { eapply (CK 32 3%nat); [replace (sp - RRFC_FRAME + 32) with (sp - 48) by lia; exact W20 | reflexivity]. }
apply Forall_cons. { eapply (CK 40 4%nat); [replace (sp - RRFC_FRAME + 40) with (sp - 40) by lia; exact W19 | reflexivity]. }
apply Forall_cons. { eapply (CK 48 5%nat); [replace (sp - RRFC_FRAME + 48) with (sp - 32) by lia; exact W18 | reflexivity]. }
apply Forall_cons. { eapply (CK 56 6%nat); [replace (sp - RRFC_FRAME + 56) with (sp - 24) by lia; exact W9 | reflexivity]. }
apply Forall_cons. { eapply (CK 64 7%nat); [replace (sp - RRFC_FRAME + 64) with (sp - 16) by lia; exact W8 | reflexivity]. }
apply Forall_cons. { eapply (CK 72 8%nat); [replace (sp - RRFC_FRAME + 72) with (sp - 8) by lia; exact W1 | reflexivity]. }
apply Forall_nil. }
assert (DSTOK : forall wh, 0 <= wh <= 12 -> region_ok ubs2segs E mem1 (YQ0b.mkRegion (Some 8%nat) 0 12 0 wh [])).
{ intros wh Hwh. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HEd.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil]. }
assert (ATOMS : atoms_ok E [ (2%nat, mkAF (CEIL_MIN + ALLOC_STACK) (2^63) 4); (8%nat, mkAF CEIL_MIN (2^63) 3); (9%nat, mkAF CEIL_MIN (2^63) 3);
(18%nat, mkAF 1 RGB_NMAX 0); (32%nat, mkAF 0 255 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HEs, HEd, HE18, HE32, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
assert (DISJ : forall wh, pairwise_disjoint E [rimg_frame; YQ0b.mkRegion (Some 8%nat) 0 12 0 wh []]).
{ intros wh. unfold rimg_frame. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite ?HE2, ?HEd. repeat split; lia. }
destruct (fmt_okb fb) eqn:Hok.
2: {
assert (HS : st_ok ubs2segs E (ss_rimg false) (mkst regs1 (Z_to_bv 64 RR_MAL) mem1 (seg_rom ubs2segs))).
{ unfold ss_rimg. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [exact FRAMEOK|]. constructor; [exact (DSTOK 0 ltac:(lia))|]. constructor.
- exact (DISJ 0).
- split; [exact ATOMS | split; exact I]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 RR_MAL) mem1 (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ RR_EPI. { wr_img_ro. }
cbn [ms_mem mkst] in HF, HJ.
jbranch ubs2tbl HS.
{ exfalso. rewrite (fmt_okb_bad_branch _ 32 fb HE32 Hfb) in Hc. congruence. }
jrun LAWS ubs2tbl_ok HS HJ. { wr_img_ro. }
cbn [ms_mem mkst] in HF0, HJ.
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
rimg_fin HS HJ Hid HX HE HE2 Hra0 (2 ^ 64 - 1) cur 0.
- intros a Ha Hn1 Hn2 Hn3.
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- apply word_mem_frame with (m := mem1); [exact Wc|]. intros i Hi.
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- lia.
- left. split; [exact Hok|]. split; [reflexivity|]. split; [exact HBc|].
intros a Ha.
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity. }
destruct (Gok eq_refl) as (G19 & G20 & G21 & G10).
pose proof (fmt_okb_range fb Hok) as Hfb34.
assert (HS : st_ok ubs2segs E (ss_rimg true) (mkst regs1 (Z_to_bv 64 RR_MAL) mem1 (seg_rom ubs2segs))).
{ unfold ss_rimg. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg
| intros H0; discriminate H0 | cbn [sv_denot]; exact G19]
| intros H0; discriminate H0 | cbn [sv_denot]; exact G20]
| intros H0; discriminate H0 | cbn [sv_denot]; exact G21]
| intros H0; discriminate H0 | cbn [sv_denot]; exact G10].
- vm_compute. reflexivity.
- constructor; [exact FRAMEOK|]. constructor; [exact (DSTOK 12 ltac:(lia))|]. constructor.
- exact (DISJ 12).
- split; [exact ATOMS | split; exact I]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 RR_MAL) mem1 (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc. { wr_img HEd. }
cbn [ms_mem mkst] in HF, HJ.
jbranch ubs2tbl HS.
2: { exfalso. rewrite (fmt_okb_bad_branch _ 32 fb HE32 Hfb) in Hc. congruence. }
clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc. { wr_img HEd. }
cbn [ms_mem mkst] in HF0, HJ.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => pose proof (st_ok_reg ubs2segs Ec ssc msc (10%bv:reg) HS) as Hr10; eval_sr_get_in Hr10 end.
rewrite (denot_mul_atoms_r _ 18 32 N fb HE18 HE32) in Hr10 by lia.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := N * fb) (spc := sp - RRFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | lia
| exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2). clear HJ.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2.
jafter_call_keep HS 42%nat regs2 mem2 HP2 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HE2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 8); [exact HEd | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq10. cbn [ms_regs mkst] in Hq10. rewrite Hres10 in Hq10. symmetry in Hq10.
destruct Hres as [[-> Hbl] | (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr)].
{
pin10 HS 0 Hq10.
jrun LAWS ubs2tbl_ok HS HJ2. { wr_img HEd. }
cbn [ms_mem mkst] in HF1, HJ2.
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
rimg_fin HS HJ2 Hid2 HX HE HE2 Hra0 0 cur 0.
- intros a Ha Hn1 Hn2 Hn3.
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi2 a Ha ltac:(lia))).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hkeep2 b m i Hbc Hi).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- apply word_mem_frame with (m := mem1); [exact Wc|]. intros i Hi.
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi2 (st + 16 + i) ltac:(lia) ltac:(lia))).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- lia.
- right. left. split; [exact Hok|]. split; [reflexivity|]. rewrite Hbl. exact HBc. }
assert (Himg2 : In (res, N * fb) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
destruct (heap_blocks_range _ _ LAWS L2 A2 _ md2 res (N * fb) HH2 Himg2 ltac:(nia)) as (Hrs0 & Hrs1 & _).
assert (Hpd2 : In (pdata, nb) (b1 ++ b2)) by (rewrite <- Hblc; exact Hpdc).
assert (Hpd2' : In (pdata, nb) (blocks L2 A2)).
{ rewrite Hbl2. apply in_app_iff in Hpd2 as [H|H]; apply in_app_iff; [left | right; right]; exact H. }
assert (Hsrc : cur + N * fb <= nb -> res + N * fb <= pdata + cur \/ pdata + cur + N * fb <= res).
{ intros Hf. destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N * fb) b2 (pdata, nb) HH2 Hbl2 Hpd2) as [Hs|Hs]; cbn [fst snd] in Hs;
[left | right]; lia. }
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_readdata. { wr_img HEd. }
cbn [ms_mem mkst] in HF1, HJ2.
jbranch ubs2tbl HS.
{ exfalso. rewrite branch_eq_U, (U_atom _ _ res Hq10), U_SLit in Hc by lia. apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. contradiction. }
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_readdata. { wr_img HEd. }
cbn [ms_mem mkst] in HF2, HJ2.
jreg HS (10%bv:reg) as D10. rewrite (HE 9%nat 9%bv eq_refl), G9 in D10.
jreg HS (11%bv:reg) as D11. rewrite Hq10 in D11.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => pose proof (st_ok_reg ubs2segs Ec ssc msc (12%bv:reg) HS) as D12; eval_sr_get_in D12 end.
rewrite (denot_mul_atoms_r _ 18 32 N fb) in D12 by first [lia | ew_havoc; assumption].
jreg HS (2%bv:reg) as D2. rewrite (HE 2%nat 2%bv eq_refl), G2 in D2.
jreg HS (1%bv:reg) as D1.
lazymatch type of HS with st_ok _ _ _ ?msc =>
assert (KEEPST : forall a, st <= a < st + 24 -> mbyte ubs2segs (ms_mem msc) a = mbyte ubs2segs mem1 a);
[ intros a Ha;
mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia);
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia);
rewrite (proj1 (Hhi2 a ltac:(lia) ltac:(lia)));
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia);
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia); reflexivity |];
assert (Hspz : spZ (ms_regs msc) = sp - RRFC_FRAME) by (unfold spZ; rewrite D2; apply unsigned_lit_small; lia)
end.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HHc.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (ubs2_readdata API IMG STK sp0 FP L A mem md L2 A2 _ md2 _ st res (N * fb) pdata nb cur);
[ exact HJ2 | rewrite D1; apply ret_ok_even; vm_compute; reflexivity | rewrite Hspz; exact Hspm
| rewrite Hspz, HRDS; lia | rewrite Hspz; lia | lia | exact Hst8
| exact D10 | exact D11 | exact D12 | rewrite HRDN; nia | lia | lia
| apply word_mem_frame with (m := mem1); [exact Wp | intros i Hi; apply KEEPST; lia]
| apply word_mem_frame with (m := mem1); [exact Wn | intros i Hi; replace (st + 8 + i) with (st + (8 + i)) by lia; apply KEEPST; lia]
| apply word_mem_frame with (m := mem1); [exact Wc | intros i Hi; replace (st + 16 + i) with (st + (16 + i)) by lia; apply KEEPST; lia]
| intros Hfit ].
rewrite Hspz, HRDS.
split; [lia|]. split; [lia|]. split.
{ intros i Hi. replace (pdata + cur + i) with (pdata + (cur + i)) by lia.
exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 pdata nb (cur + i) HHc Hpd2' ltac:(lia))). }
split; [lia|]. split; [nia|]. split.
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res (N * fb) i HHc Himg2 Hi)). }
split.
{ intros a Ha. replace a with (res + (a - res)) by lia. apply (Hwr (blocks L2 A2)); [exact Himg2 | lia]. }
split; [exact (Hsrc Hfit)|]. split; [left; lia|]. left; lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hcase & Hout3).
rewrite Hspz, HRDS in Hout3. rewrite D1.
jafter_call_ro HS 64%nat regs3 mem3 HP3 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_pointwise ubs2segs _ _ _ 2); [exact HE2 | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. apply Hout3; [lia | lia | lia | intros [_ Hx]; lia].
- eapply (region_kept_pointwise ubs2segs _ _ _ 8); [exact HEd | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. apply Hout3; [lia | lia | lia | intros [_ Hx]; lia]. }
clear HS. rename HS2 into HS.
destruct Hcase as [(Hfit & R10 & Wc3 & Hcp) | (Hnofit & R10 & Wc3)].
{
jreg HS (10%bv:reg) as Q10. cbn [ms_regs mkst] in Q10. rewrite R10 in Q10. symmetry in Q10.
pin10 HS 0 Q10.
jrun LAWS ubs2tbl_ok HS HJ3. { wr_img_ro. }
cbn [ms_mem mkst] in HF3, HJ3.
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))). }
rimg_fin HS HJ3 Hid2 HX HE HE2 Hra0 1 (cur + N * fb) res.
- intros a Ha Hn1 Hn2 Hn3.
mb_frame HF3; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hout3 a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [_ Hx]; lia)).
mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi2 a Ha ltac:(lia))).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
assert (Hbn : In (b, m) (b1 ++ b2)) by (rewrite <- Hblc; exact Hbc).
pose proof (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, N * fb) b2 (b, m) HH2 Hbl2 Hbn) as Hbs. cbn [fst snd] in Hbs.
mb_frame HF3; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hout3 (b + i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [_ Hx]; lia)).
mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hkeep2 b m i Hbc Hi).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- apply word_mem_frame with (m := mem3); [exact Wc3|]. intros i Hi.
mb_frame HF3; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- lia.
- right. right. split; [exact Hok|]. split; [reflexivity|]. split; [| split; [lia | split]].
+ rewrite <- (Z.add_0_r dst). eapply (st_chunk_word _ _ _ 1%nat _ 8%nat 0 _ dst res HS); [reflexivity | reflexivity | cbv; auto 10 | | | lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HEd. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, Hq10, Z_to_bv_bv_unsigned. reflexivity. }
+ eapply (st_chunk_val ubs2segs _ _ _ 1%nat _ 8%nat 8 4%N _ dst fb HS); [reflexivity | reflexivity | cbv; auto 10 | | | cbn; lia | cbn; lia].
{ repeat (rewrite ew_havoc_old; [|cbv; lia]). exact HEd. }
{ cbn [sv_denot]. repeat (rewrite ew_havoc_old; [|cbv; lia]). rewrite !Z.add_0_r, HE32, Z_to_bv_bv_unsigned. reflexivity. }
+ rewrite Hbl2, (Z.mul_comm fb N). eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
apply perm_skip. rewrite <- Hblc. exact HBc. }
jreg HS (10%bv:reg) as Q10. cbn [ms_regs mkst] in Q10. rewrite R10 in Q10. symmetry in Q10.
pin10 HS 18446744073709551615 Q10.
jrun_to LAWS ubs2tbl_ok HS HJ3 ubs2_A_free. { wr_img_ro. }
cbn [ms_mem mkst] in HF3, HJ3.
jreg HS (10%bv:reg) as F10. rewrite Hq10 in F10.
jreg HS (2%bv:reg) as F2. rewrite (HE 2%nat 2%bv eq_refl), G2 in F2.
jreg HS (4%bv:reg) as F4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in F4.
jreg HS (1%bv:reg) as F1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS ubs2_errno_low IMG (aa_free API)) with (a := res) (n := N * fb) (spc := sp - RRFC_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Himg2 | exact F10
| exact F2 | lia | exact Hspm | lia | lia | exact F4 | exact F1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin. exfalso. apply Hbase in Hin.
apply (fresh_not_in API L2 A2 _ md2 b1 b2 res (N * fb) HH2 Hbl2 ltac:(nia)). rewrite <- Hblc.
eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hin]. }
intros c' (L3 & A3 & regs4 & mem4 & md3 & -> & HJ4 & HP4 & Hrm4 & Hkeep4 & Hhi4 & Hid4).
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep4, Hhi4. cbn [ms_regs ms_mem mkst] in HP4, Hkeep4, Hhi4, HJ4, Hrm4.
assert (HB3 : Permutation (blocks L3 A3) Bb).
{ eapply perm_after_rm1; [| exact Hrm4]. rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
apply perm_skip. rewrite <- Hblc. exact HBc. }
jafter_call_keep HS 86%nat regs4 mem4 HP4 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HE2 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 8); [ew_havoc; exact HEd | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ4. { wr_img_ro. }
cbn [ms_mem mkst] in HF4, HJ4.
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4)))). }
rimg_fin HS HJ4 Hid4 HX HE HE2 Hra0 0 nb 0.
- intros a Ha Hn1 Hn2 Hn3.
mb_frame HF4; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi4 a Ha ltac:(lia))).
mb_frame HF3; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hout3 a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [Hx _]; lia)).
mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi2 a Ha ltac:(lia))).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac mem1 mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
assert (Hb3 : In (b, m) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | exact Hb]).
mb_frame HF4; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hkeep4 b m i Hb3 Hi).
mb_frame HF3; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hout3 (b + i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [Hx _]; lia)).
mb_frame HF2; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF1; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (Hkeep2 b m i Hbc Hi).
mb_frame HF0; try (rewrite ?HE2, ?HEs, ?HEd; lia).
mb_frame HF; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- apply word_mem_frame with (m := mem3); [exact Wc3|]. intros i Hi.
mb_frame HF4; try (rewrite ?HE2, ?HEs, ?HEd; lia).
rewrite (proj1 (Hhi4 (st + 16 + i) ltac:(lia) ltac:(lia))).
mb_frame HF3; try (rewrite ?HE2, ?HEs, ?HEd; lia). reflexivity.
- lia.
- right. left. split; [exact Hok|]. split; [reflexivity|]. exact HB3.
Qed.
End S.
End c.
