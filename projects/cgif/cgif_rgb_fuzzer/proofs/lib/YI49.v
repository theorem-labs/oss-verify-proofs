(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g YI3h YI3d
YI4v YI46 YI4g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_mul_lit_r : forall E a k x, U E a = x -> 0 <= k < 2 ^ 32 -> 0 <= x -> x * k < 2 ^ 64 -> U E (SMd M_MUL a (SLit k)) = x * k.
Proof.
intros E a k x Ha Hk Hx Hkx. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, Ha. rewrite (zcanon_id k) by (unfold M64; lia).
apply zcanon_id. unfold M64; nia.
Qed.
Lemma U_sll2 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 60 -> U E (SAlu ALU_SLL (SOff n 0) (SLit 2)) = x * 4.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n x Hn) by lia. change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. apply zcanon_id. unfold M64; lia.
Qed.
Definition ss_LD : sstate := mkSS PC_LD sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 5136 72 80 [] ;
YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 24 (CVal 8 (SOff 32%nat 0)); mkChunk 32 (CVal 8 (SOff 33%nat 0))] ] None
(mkFacts [(2%nat, mkAF CEIL_MIN (2^63) 4); (18%nat, mkAF 521 (2^24) 0)] [] []).
Definition ss_R1 : sstate := mkSS PC_R1 sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 32 (CVal 8 (SOff 33%nat 0))] ] None
(mkFacts [(18%nat, mkAF 521 (2^24) 0)] [] []).
Section d.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Hypothesis REALLOC : realloc_realizes src2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Local Notation AT_LD := (at_LD API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_R1 := (at_R1 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_R2 := (at_R2 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation KEEPB := (keepb r g bef beffmt s N img fmt rest).
Local Notation RZ_MEM_KEPT := (rz_mem_kept API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation RZ_MEM_ZSUM := (rz_mem_zsum regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_HT := (rz_mem_ht regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RINV_CALL := (rgba_inv_call API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Section e.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht).
Let T' : Z := getNextPrimePower2 (ch_T C).
Hypothesis KR1 : forall regs1 Lc Ac memc mdc p1, AT_R1 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_R1) memc (seg_rom src2segs)) mdc) POST.
Hypothesis KR2 : forall regs1 Lc Ac memc mdc p1 x1, AT_R2 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_R2) memc (seg_rom src2segs)) mdc) POST.
Theorem LD_stretch : forall regs1 Lc Ac memc mdc, AT_LD regs1 Lc Ac memc mdc i ha pnew fimg imgl C ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_LD) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc [HAT G18]. pose proof HAT as (HINV & HREGS & Hfmt & Hi & Hha & G11 & G5 & G9 & G20 & G8 & G21 & G22 & HTlt & HMEM).
destruct (rz_mem_of_RS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc i ha pnew fimg imgl C HAT) as (RZM & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcht & _ & _ & _ & Hz & _ & _ & HB).
pose proof Hcht as (Hobjc & _ & Hinv & HT & Hch & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity. assert (HRSv : REALLOC_STACK = 8256) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). fold T' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
pose proof (proj2 (proj2 (chain_sizes T' Hch'))) as RT4'. pose proof (proj2 (proj2 (chain_sizes (ch_T C) Hch))) as RT4.
set (T := ch_T C) in *.
assert (HT2 : T + 2048 <= T').
{ assert (HT5 : T = 524309 \/ T = 1048583 \/ T = 2097169 \/ T = 4194319 \/ T = 8388617).
{ pose proof Hch as Hch0. cbv [ts_chain In] in Hch0. unfold MAX_TABLE_SIZE in HTlt. clear - Hch0 HTlt. lia. }
enough (HT2' : T + 2048 <= getNextPrimePower2 T) by exact HT2'.
clear - HT5. destruct HT5 as [E|[E|[E|[E|E]]]]; rewrite E; vm_compute; discriminate. }
assert (ET' : T' = getNextPrimePower2 T) by reflexivity. rewrite <- ET' in G18. clearbody T'.
pose proof (obj_at_nth src2segs memc (ch_c C) LAY_Cht _ 3 _ _ Hobjc eq_refl eq_refl) as [Bc3 Rp]. cbn [fst snd] in Bc3, Rp.
pose proof (obj_at_nth src2segs memc (ch_c C) LAY_Cht _ 4 _ _ Hobjc eq_refl eq_refl) as [Bc4 Rx]. cbn [fst snd] in Bc4, Rx.
change (N.to_nat 8) with 8%nat in Bc3, Bc4. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rp, Rx.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ [(ch_p C, 3 * T); (ch_x C, 4 * T)]) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]. }
assert (HBc : In (ch_c C, CHT_SIZE) (blocks Lc Ac)) by (apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
assert (HBp : In (ch_p C, 3 * T) (blocks Lc Ac)) by (apply INB; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE HHc HBc ltac:(unfold CHT_SIZE; lia)) as (Rc0 & Rc1 & _). unfold CHT_SIZE in Rc1.
assert (HBp0 : ~ In (ch_p C, 3 * T) (blocks L A)).
{ apply (tmp_not_entry API L A Lc Ac memc mdc (ch_p C, 3 * T) BASE0 ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ [(ch_p C, 3 * T); (ch_x C, 4 * T)]) HHc); [| exact HB0 | | cbn; lia].
- unfold rz_blocks, keepb in RZB. rewrite <- !app_assoc in RZB. exact RZB.
- apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_p C; ch_x C] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_p C)) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (ch_x C)) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HE18 : ew E 18 = Z_to_bv 64 T') by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE5 : ew E 5 = Z_to_bv 64 ha) by (rewrite (HE 5%nat 5%bv eq_refl); exact G5).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E ss_LD (mkst regs1 (Z_to_bv 64 PC_LD) memc (seg_rom src2segs))).
{ unfold ss_LD. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
+ rewrite HU2. split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [|constructor]. intros o Ho. apply Hstw. unfold sp, sp0 in *. lia.
+ rewrite HU20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_p C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc3.
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_x C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc4.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU20.
unfold sp, sp0 in *. repeat split; try exact I. clear - Rc1 Hceil HRv HFv. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE18, unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. unfold sp, sp0 in *. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_LD) memc (seg_rom src2segs))) in HJ. clearbody E.
jrun_to LAWS src2tbl_ok HS HJ src2_A_realloc.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold sp, sp0 in *; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 72 <= a < SP + 80) -> mbyte src2segs (ms_mem ms) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF; [reflexivity | rewrite HU2; lia | lia]. }
assert (S72 : slot regs0 (ms_mem ms) SL_72 ha).
{ unfold slot, SL_72. apply (st_chunk_word_g src2segs E _ _ 0%nat _ 2%nat 72 (SOff 5 0) SP ha HS eq_refl eq_refl ltac:(left; reflexivity) HU2); [|].
- cbn [sv_denot]. rewrite Z.add_0_r, HE5, Z_to_bv_bv_unsigned. reflexivity.
- clear - Hha. lia. }
jreg HS (10%bv:reg) as Ma0. rewrite HE32 in Ma0.
assert (Ma1 : getr (ms_regs ms) 11 = Z_to_bv 64 (3 * T')).
{ eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. rewrite (Z.mul_comm 3 T'). apply (U_mul_lit_r E _ 3 T'); [apply (U_atom E 18 T' HE18); lia | lia | lia | lia]. }
assert (M23 : getr (ms_regs ms) 23 = Z_to_bv 64 (3 * T')).
{ eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. rewrite (Z.mul_comm 3 T'). apply (U_mul_lit_r E _ 3 T'); [apply (U_atom E 18 T' HE18); lia | lia | lia | lia]. }
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 22; 18]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jrealloc_at _ _ LAWS src2_errno_low IMG REALLOC src2_A_realloc) with (pa := ch_p C) (nold := 3 * T) (n := 3 * T') (spc := SP);
[ reflexivity | exact HS | reflexivity | reflexivity | exact HJ | exact HBp | exact HBp0 | exact Ma0 | exact Ma1
| unfold MMAP_THRESHOLD; lia | unfold MMAP_THRESHOLD; lia | unfold PGSZ; lia
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & p1 & -> & HJ2 & HP2 & Hr10 & Hres & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hres, Hhi2, HJ2.
change (ms_segs src2_msyms) with src2segs in Hres, Hhi2.
pose proof (proj1 HJ2) as HH2.
assert (RZB' : Permutation (blocks Lc Ac) ((KEEPB pnew fimg C ++ [(ch_x C, 4 * T)]) ++ [(ch_p C, 3 * T)])).
{ eapply Permutation_trans; [exact RZB|]. rewrite <- app_assoc. apply Permutation_app_head. apply perm_swap. }
destruct (realloc_post_perm (KEEPB pnew fimg C ++ [(ch_x C, 4 * T)]) (ch_p C, 3 * T) (blocks L2 A2) (blocks Lc Ac) memc mem2 p1 (3 * T') RZB') as [HB2 KB2].
{ assert (BLK : forall a k j, In (a, k) (blocks Lc Ac) -> 0 <= j < k -> mbyte src2segs (ms_mem ms) (a + j) = mbyte src2segs memc (a + j)).
{ intros a k j Ha Hj. destruct (heap_blocks src2_msyms MR LAWS Lc Ac memc mdc a k j HHc Ha Hj) as (_ & H1 & H2 & _). apply K1; unfold sp, sp0 in *; lia. }
destruct Hres as (b1 & b2 & Eb & Hc). exists b1, b2. split; [exact Eb|].
destruct Hc as [(E0 & EB & Hk) | (Hnz & Hal & Ec & Hk)].
- left. split; [exact E0|]. split; [exact EB|]. intros a k j Ha Hj. rewrite (Hk a k j Ha Hj). exact (BLK a k j Ha Hj).
- right. split; [exact Hnz|]. split; [exact Hal|]. split; [exact Ec|]. intros a k j Ha Hj. rewrite (Hk a k j Ha Hj). apply (BLK a k j); [| exact Hj].
rewrite Eb. apply in_app_iff in Ha. apply in_app_iff. destruct Ha; [left | right; right]; assumption. }
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> ~ (SP + 72 <= a < SP + 80) -> mbyte src2segs mem2 a = mbyte src2segs memc a).
{ intros a Ha Hs Hna. rewrite (proj1 (Hhi2 a Ha ltac:(lia))). apply K1; [lia | exact Hna]. }
change (Z_to_bv 64 80116) with (Z_to_bv 64 PC_R1). change (ms_segs src2_msyms) with src2segs.
apply (KR1 regs2 L2 A2 mem2 md2 p1). unfold at_R1.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { unfold keepb in HB2. rewrite <- !app_assoc in HB2. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2). intros a Ha Hs. apply KH2; [exact Ha | lia | lia]. }
split; [split; [exact Hfmt|]; split; [exact Hi|]; split; [exact Hha | exact ET']|].
split. { unfold rz_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G22. }
split; [exact Hr10|].
split; [rewrite RP by (vm_compute; reflexivity); exact M23|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 18%bv ltac:(cbv; auto 20)); exact G18|].
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C [(ch_p C, 3 * T); (ch_x C, 4 * T)] i HHc); [unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Hfmt | exact RZB | exact RZM | | | ].
- intros a Ha Hs Hn1 _. apply KH2; [exact Ha | exact Hs | exact Hn1].
- intros b n k Hb Hk. apply (KB2 b n k); [apply in_app_iff; left; apply (keepb_sub r g bef beffmt s N img fmt rest); exact Hb | exact Hk].
- exact (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM). }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 (ms_mem ms)); [exact S72|]. intros k Hk. apply (proj1 (Hhi2 k ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia))). }
split. { apply (rz_struct_kept r g bef beffmt s N img fmt rest memc mem2 pnew fimg C); [exact RZS|]. intros b n k Hb Hk. apply (KB2 b n k); [apply in_app_iff; left; exact Hb | exact Hk]. }
unfold rz_blocks. eapply Permutation_trans; [exact HB2|]. rewrite <- app_assoc. apply Permutation_app_head. apply perm_swap.
Qed.
Theorem R1_stretch : forall regs1 Lc Ac memc mdc p1, AT_R1 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_R1) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 HAT.
destruct HAT as (HINV & (Hfmt & Hi & Hha & ET') & (HREGS & G9 & G20 & G8 & G21 & G22) & G10 & G23 & G18 & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity. assert (HRSv : REALLOC_STACK = 8256) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
pose proof (proj2 (proj2 (chain_sizes T' Hch'))) as RT4'. pose proof (proj2 (proj2 (chain_sizes (ch_T C) Hch))) as RT4.
set (T := ch_T C) in *.
assert (HT2 : T + 2048 <= T').
{ assert (HT5 : T = 524309 \/ T = 1048583 \/ T = 2097169 \/ T = 4194319 \/ T = 8388617).
{ pose proof Hch as Hch0. cbv [ts_chain In] in Hch0. clear - Hch0 HTlt. lia. }
rewrite ET'. clear - HT5. destruct HT5 as [E|[E|[E|[E|E]]]]; rewrite E; vm_compute; discriminate. }
pose proof (obj_at_nth src2segs memc (ch_c C) LAY_Cht _ 4 _ _ RZS eq_refl eq_refl) as [Bc4 Rx]. cbn [fst snd] in Bc4, Rx.
change (N.to_nat 8) with 8%nat in Bc4. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rx.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * T) p1 (3 * T'); (ch_x C, 4 * T)]) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]. }
assert (HBc : In (ch_c C, CHT_SIZE) (blocks Lc Ac)) by (apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
assert (HBx : In (ch_x C, 4 * T) (blocks Lc Ac)) by (apply INB; apply in_app_iff; right; right; left; reflexivity).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE HHc HBc ltac:(unfold CHT_SIZE; lia)) as (Rc0 & Rc1 & _). unfold CHT_SIZE in Rc1.
assert (HBx0 : ~ In (ch_x C, 4 * T) (blocks L A)).
{ apply (tmp_not_entry API L A Lc Ac memc mdc (ch_x C, 4 * T) BASE0 ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ [rbk (ch_p C, 3 * T) p1 (3 * T'); (ch_x C, 4 * T)]) HHc); [| exact HB0 | | cbn; lia].
- unfold rz_blocks, keepb in RZB. rewrite <- !app_assoc in RZB. exact RZB.
- apply in_app_iff. right. apply in_app_iff. right. right. left. reflexivity. }
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_p C; ch_x C] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE33 : ew E 33 = Z_to_bv 64 (ch_x C)) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HE18 : ew E 18 = Z_to_bv 64 T') by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE10 : ew E 10 = Z_to_bv 64 p1) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E ss_R1 (mkst regs1 (Z_to_bv 64 PC_R1) memc (seg_rom src2segs))).
{ unfold ss_R1. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HU20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_x C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc4.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE18, unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_R1) memc (seg_rom src2segs))) in HJ. clearbody E.
jrun_to LAWS src2tbl_ok HS HJ src2_A_realloc. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x) end).
jreg HS (10%bv:reg) as Ma0. rewrite HE33 in Ma0.
assert (Ma1 : getr (ms_regs ms) 11 = Z_to_bv 64 (4 * T')).
{ eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. rewrite (Z.mul_comm 4 T'). apply (U_sll2 E 18 T' HE18). lia. }
assert (M25 : getr (ms_regs ms) 25 = Z_to_bv 64 (4 * T')).
{ eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. rewrite (Z.mul_comm 4 T'). apply (U_sll2 E 18 T' HE18). lia. }
jreg HS (26%bv:reg) as M26. rewrite HE10 in M26.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 22; 18; 23]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jrealloc_at _ _ LAWS src2_errno_low IMG REALLOC src2_A_realloc) with (pa := ch_x C) (nold := 4 * T) (n := 4 * T') (spc := SP);
[ reflexivity | exact HS | reflexivity | reflexivity | exact HJ | exact HBx | exact HBx0 | exact Ma0 | exact Ma1
| unfold MMAP_THRESHOLD; lia | unfold MMAP_THRESHOLD; lia | unfold PGSZ; lia
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & x1 & -> & HJ2 & HP2 & Hr10 & Hres & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hres, Hhi2, HJ2.
change (ms_segs src2_msyms) with src2segs in Hres, Hhi2. rewrite Em in Hres, Hhi2.
pose proof (proj1 HJ2) as HH2.
assert (RZB' : Permutation (blocks Lc Ac) ((KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * T) p1 (3 * T')]) ++ [(ch_x C, 4 * T)])).
{ eapply Permutation_trans; [exact RZB|]. rewrite <- app_assoc. apply Permutation_refl. }
destruct (realloc_post_perm (KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * T) p1 (3 * T')]) (ch_x C, 4 * T) (blocks L2 A2) (blocks Lc Ac) memc mem2 x1 (4 * T') RZB' Hres) as [HB2 KB2].
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte src2segs mem2 a = mbyte src2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
change (Z_to_bv 64 80136) with (Z_to_bv 64 PC_R2). change (ms_segs src2_msyms) with src2segs.
apply (KR2 regs2 L2 A2 mem2 md2 p1 x1). unfold at_R2.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { unfold keepb in HB2. rewrite <- !app_assoc in HB2. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [split; [exact Hfmt|]; split; [exact Hi|]; split; [exact Hha | exact ET']|].
split. { unfold rz_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G22. }
split; [exact Hr10|].
split; [rewrite RP by (vm_compute; reflexivity); exact M26|].
split; [rewrite RP by (vm_compute; reflexivity); exact M25|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 23%bv ltac:(cbv; auto 20)); exact G23|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 18%bv ltac:(cbv; auto 20)); exact G18|].
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C [rbk (ch_p C, 3 * T) p1 (3 * T'); (ch_x C, 4 * T)] i HHc); [unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Hfmt | exact RZB | exact RZM | | | exact Hz].
- intros a Ha Hs _ _. apply KH2; [exact Ha | exact Hs].
- intros b n k Hb Hk. apply (KB2 b n k); [apply in_app_iff; left; apply (keepb_sub r g bef beffmt s N img fmt rest); exact Hb | exact Hk]. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KH2; unfold sp, sp0 in *; lia. }
split. { apply (rz_struct_kept r g bef beffmt s N img fmt rest memc mem2 pnew fimg C); [exact RZS|]. intros b n k Hb Hk. apply (KB2 b n k); [apply in_app_iff; left; exact Hb | exact Hk]. }
unfold rz_blocks. eapply Permutation_trans; [exact HB2|]. rewrite <- app_assoc. apply Permutation_refl.
Qed.
End e.
End d.
End c.
