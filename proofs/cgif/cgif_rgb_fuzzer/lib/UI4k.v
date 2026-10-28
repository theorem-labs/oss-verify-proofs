(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI04 YI05
UI1e UI39 UI1i UI57 UI1h YI0x UI16 UO0e
YI07 YP14 YI08 YI0c YI0g UI3h UI3d UI4v UIZm
YI0h UI4l UI4j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_LR : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 2772).
Lemma mod4_of16 : forall a k, a mod 16 = 0 -> (a + 4 * k) mod 4 = 0.
Proof.
intros a k Ha. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists k; lia].
apply Z.mod_divide in Ha; [|lia]. destruct Ha as [q Hq]. exists (4 * q). lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_Q0b1 : sstate :=
mkSS PC_LH sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 8 (CVal 8 (SOff 33 0)); mkChunk 16 (CVal 8 (SOff 34 0)); mkChunk 24 (CVal 8 (SOff 35 0)); mkChunk 44 (CVal 4 (SOff 32 0))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (9%nat, mkAF 0 (2^26) 0); (20%nat, mkAF 4096 (CEIL_MAX - 48) 4); (32%nat, mkAF 0 (2^24) 0);
(35%nat, mkAF 4096 CEIL_MAX 0); (36%nat, mkAF 4096 (CEIL_MAX + 2^26) 0) ]
[ mkAC BC_GEU (SOff 36%nat 0) (SOff 35%nat 0) ]
[ (SAlu ALU_ADD (SAlu ALU_AND (SOff 9%nat 0) (SLit (2 ^ 32 - 1))) (SOff 35%nat 0), SOff 36%nat 0) ]).
Definition ss_Q0b2 (al : list (sv * sv)) : sstate :=
mkSS PC_LR sr_atoms
[ YQ0b.mkRegion (Some 32%nat) 0 4 0 0 [mkChunk 0 (CVal 4 (SOff 33 0))] ;
YQ0b.mkRegion (Some 38%nat) 0 4 0 4 [] ;
YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 0 (CVal 8 (SOff 34 0)); mkChunk 24 (CVal 8 (SOff 36 0)); mkChunk 40 (CVal 4 (SOff 35 0))] ;
YQ0b.mkRegion (Some 2%nat) 0 120 0 0 [mkChunk 96 (CVal 8 (SOff 37 0))] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 0 (2^24) 0); (19%nat, mkAF 0 (2^26) 0);
(38%nat, mkAF 4096 (CEIL_MAX - 4) 2); (32%nat, mkAF 4096 (CEIL_MAX - 4) 2); (33%nat, mkAF 0 RGB_NMAX 0);
(20%nat, mkAF 4096 (CEIL_MAX - 48) 4); (34%nat, mkAF 4096 CEIL_MAX 4); (35%nat, mkAF 256 (2^24) 0);
(37%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0) ] [ mkAC BC_GEU (SOff 32%nat 0) (SOff 34%nat 0) ] al).
Definition q0_alias : list (sv * sv) := [ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10%nat 0) (SLit 2)) (SOff 34%nat 0), SOff 32%nat 0);
(SAlu ALU_ADD (SOff 24%nat 0) (SOff 19%nat 0), SOff 38%nat 0) ].
Section e.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis COLH : col_hash_spec API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation AT_LH := (at_LH API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Definition K_LHn (n : nat) (i : Z) : Prop := forall regs1 Lc Ac memc mdc ha pnew fimg imgl C fdp,
ht_cnt (ch_H C) - i <= Z.of_nat n -> AT_LH regs1 Lc Ac memc mdc i ha pnew fimg imgl C fdp -> SR ubs2segs (cfg_at regs1 PC_LH memc mdc) POST.
Lemma LH_base : forall i, K_LHn 0 i.
Proof. intros i regs1 Lc Ac memc mdc ha pnew fimg imgl C fdp Hn HAT. destruct HAT as (_ & _ & _ & _ & _ & _ & Hi & _). exfalso. cbn in Hn. lia. Qed.
Lemma LH_body : forall n i,
K_CR API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
(forall j, K_LHn n j) -> K_LHn (S n) i.
Proof.
intros n i KCR IH regs1 Lc Ac memc mdc ha pnew fimg imgl C fdp Hn HAT. unfold K_CR, cfg_atF in KCR. unfold cfg_at.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hc256 & Hi & G9 & G19 & G22 & G23 & G24 & G25 & G18 & G26 & G27 & G20 & G8 & G21
& Hslm & Hslq & Hs96 & Hfc & Hobj & Hcg & Himg & Hst & Harr & Hinv & HTT & Hts & Hsum & Hdense & Hpres & Hpnz & Hfnz & Hfdnz & Hfd16 & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HHt & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HCSTK : COLHASH_STK = 64) by reflexivity.
assert (HCHT : CHT_SIZE = 48) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity. assert (HRFCv : RGBFC_SIZE = 24) by reflexivity.
assert (HMTS : MAX_TABLE_SIZE = 16777216) by reflexivity.
destruct C as [c f h u p x T hS uS TS HT ent]. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent] in *.
pose proof (ts_chain_ok T Hts) as (HT1 & HT4 & HT2).
pose proof Hinv as ((LenU & LenK & LenF & LenX & LenP) & (Hcnt & Helen & _) & (_ & KeysB & PalB) & _). rewrite HTT in *.
set (cnt := ht_cnt HT) in *.
destruct (ent_slot HT ent Hinv i ltac:(subst cnt; lia)) as (hh & Hin & Hci & He & Hpc & Hf1).
pose proof Hin as [Rhh Huse]. rewrite HTT in Rhh.
set (fv := freq HT hh) in *.
assert (Hfv : getz (map snd ent) i = fv).
{ unfold getz. apply nth_error_nth. rewrite nth_error_map, He. reflexivity. }
pose proof (zsum_pos_le ent (Z.to_nat i) _ _ (ent_freq_pos HT ent Hinv) He) as Hfle. cbn [snd] in Hfle.
assert (Rfv : 1 <= fv <= N) by (subst fv; lia).
assert (Hprobe : probe T (ht_used HT) (ht_keys HT) (palc HT i) = Some hh).
{ rewrite Hpc, <- HTT, <- probe_of_htab. apply (find_present HT ent Hinv hh Hin). }
destruct Harr as (Af & Ak & Au & Ap & Ax).
assert (Vfv : val_mem ubs2segs memc (f + 4 * hh) 4 fv /\ 0 <= fv < 2 ^ 32).
{ subst fv. unfold freq. exact (arr32_getz _ _ _ _ hh Af ltac:(rewrite LenF; lia)). }
destruct Vfv as [Vfv Rfv32].
set (KEEP := (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]) ++ ((c, CHT_SIZE) :: cht_blocks f h u p x T)) in *.
assert (Hfd_hd : Permutation (blocks Lc Ac) ((fdp, 4 * cnt) :: KEEP)).
{ eapply Permutation_trans; [exact HB|]. unfold cht_blks. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T]. subst KEEP.
rewrite !app_assoc. apply Permutation_sym. apply Permutation_cons_append. }
assert (Hkeep_in : forall b m, In (b, m) KEEP -> In (b, m) (blocks Lc Ac)).
{ intros b m Hbm. eapply Permutation_in; [apply Permutation_sym; exact Hfd_hd|]. right. exact Hbm. }
assert (Hfdis : forall b m, In (b, m) KEEP -> fdp + 4 * cnt <= b \/ b + m <= fdp).
{ intros b m Hbm. pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (fdp, 4 * cnt) KEEP (b, m) HHc Hfd_hd Hbm) as X. cbn [fst snd] in X. lia. }
assert (HBfd : In (fdp, 4 * cnt) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact Hfd_hd | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fdp (4 * cnt) HHc HBfd ltac:(lia)) as (Rfd0 & Rfd1 & _).
assert (Hfd_tmp : ~ In (fdp, 4 * cnt) (blocks L A)).
{ exact (proj2 (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc KEEP [(fdp, 4 * cnt)] fdp (4 * cnt) HHc
ltac:(eapply Permutation_trans; [exact Hfd_hd | apply Permutation_cons_append]) HBent
ltac:(intros x1 Hx1; subst KEEP; apply in_app_iff; left; apply in_app_iff; left; exact Hx1) ltac:(left; reflexivity) ltac:(lia))). }
assert (ARR : forall b m, In (b, m) (cht_blocks f h u p x T) -> In (b, m) KEEP) by (intros b m Hbm; subst KEEP; apply in_app_iff; right; right; exact Hbm).
assert (HcK : In (c, CHT_SIZE) KEEP) by (subst KEEP; apply in_app_iff; right; left; reflexivity).
pose proof (Hkeep_in _ _ HcK) as HBc. rewrite HCHT in HBc.
destruct (heap_blocks_range _ _ LAWS _ _ _ _ c 48 HHc HBc ltac:(lia)) as (Rc0 & Rc1 & Rc16).
assert (Hrk : In (r, RGB_SIZE) KEEP) by (subst KEEP; apply in_app_iff; left; apply in_app_iff; left; left; reflexivity).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc (Hkeep_in _ _ Hrk) ltac:(lia)) as (Rr0 & Rr1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ f (4 * T) HHc (Hkeep_in _ _ (ARR f (4 * T) ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Rf0 & Rf1 & Rf16).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ h (3 * T) HHc (Hkeep_in _ _ (ARR h (3 * T) ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Rh0 & Rh1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ u T HHc (Hkeep_in _ _ (ARR u T ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Ru0 & Ru1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ p (3 * T) HHc (Hkeep_in _ _ (ARR p (3 * T) ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Rp0 & Rp1 & _).
assert (HfN2 : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HNmax HNMv; nia).
assert (HBfi : In (fimg, N) KEEP) by (subst KEEP; apply in_app_iff; left; apply in_app_iff; right; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HHc (Hkeep_in _ _ HBfi) ltac:(lia)) as (Rfi0 & Rfi1 & _).
assert (Hib : img_block img fmt N = [(img, fmt * N)]) by (unfold img_block, fmt_okb; destruct Hfmt as [-> | ->]; reflexivity).
assert (HimgK : In (img, fmt * N) KEEP).
{ subst KEEP. apply in_app_iff. left. apply in_app_iff. left. unfold BASE. rewrite Hib. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
pose proof Hal0 as Hal16. unfold UI4v.sp0 in Hal16, Hclo, Hceil, H63, Hstw, HJ.
set (sp0 := spZ regs0) in *. assert (Hsp0 : sp0 = spZ regs0) by reflexivity.
assert (Hspv : sp regs0 = sp0 - 5168) by (unfold sp, UI4v.sp0, RGBA_FRAME; lia).
assert (Hsp16 : (sp0 - 5168) mod 16 = 0).
{ replace (sp0 - 5168) with (sp0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal16 | lia]. }
set (KQ := fun m : word -> option byte => forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 - 64 <= a < sp0 - 5168) -> ~ (fdp + 4 * i <= a < fdp + 4 * i + 4) ->
mbyte ubs2segs m a = mbyte ubs2segs memc a).
assert (KEPT : forall m, KQ m ->
(forall b n k, In (b, n) KEEP -> 0 <= k < n -> mbyte ubs2segs m (b + k) = mbyte ubs2segs memc (b + k)) /\
(forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 <= x0 -> mbyte ubs2segs m x0 = mbyte ubs2segs memc x0)).
{ intros m Hm. split.
- intros b n' k Hbn Hk. destruct (blocks_range _ _ LAWS Lc Ac memc mdc b n' HHc (Hkeep_in _ _ Hbn)) as [Hb0 Hb1].
pose proof (Hfdis b n' Hbn) as Hbd. apply Hm; lia.
- intros x0 Hx Hlx. apply Hm; lia. }
assert (TRANS : forall m, KQ m ->
rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac m mdc \/ True ->
slots_mid regs0 cfp N m pnew fimg /\ slots_q regs0 W bef beffmt img fmt fattr m ha /\ slot regs0 m SL_96 (2 ^ 64 - 1 - fdp) /\ fcfg_at regs0 fattr delay m fimg 0 0 /\
rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur m /\ cgif_at m g s /\ img_at N img fmt m imgl /\
obj_at ubs2segs m c LAY_Cht [f; h; u; p; x; cnt; T] /\ cht_arrays ubs2segs m f h u p x HT /\
(forall j, 0 <= j < i -> val_mem ubs2segs m (fdp + 4 * j) 4 (getz (map snd ent) j))).
{ intros m Hm _. destruct (KEPT m Hm) as [KB KH].
split. { destruct Hslm as (S1 & S2 & S3 & S4). unfold slots_mid.
repeat split; (eapply slot_kept; [eassumption | unfold SL_N, SL_cfp, SL_new, SL_fimg; lia | lia | unfold SL_N, SL_cfp, SL_new, SL_fimg; lia | intros x0 Hx0 Hlx; apply KH; lia]). }
split. { destruct Hslq as ((S1 & S2 & S3 & S4 & S5) & S6 & S7). unfold slots_q, slots_h.
repeat split; (eapply slot_kept; [eassumption | unfold SL_64, SL_88, SL_104, SL_112, SL_120, SL_32, SL_40; lia | lia | unfold SL_64, SL_88, SL_104, SL_112, SL_120, SL_32, SL_40; lia | intros x0 Hx0 Hlx; apply KH; lia]). }
split. { eapply slot_kept; [exact Hs96 | unfold SL_96; lia | lia | unfold SL_96; lia | intros x0 Hx0 Hlx; apply KH; lia]. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 32); [exact Hfc | reflexivity |]. intros k Hk. apply KH; unfold OFF_fcfg; lia. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros k Hk. apply (KB r RGB_SIZE k Hrk Hk). }
split. { eapply (cgif_at_kept _ _ g s N KEEP); [| exact Hcg | exact KB]. subst KEEP. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { split; [|exact (proj2 Himg)]. eapply arr8_frame; [exact (proj1 Himg)|]. intros a Ha. replace a with (img + (a - img)) by lia.
apply (KB img (fmt * N)); [exact HimgK | rewrite (proj2 Himg) in Ha; lia]. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact Hst | reflexivity |]. intros k Hk. apply (KB c CHT_SIZE k HcK Hk). }
split. { split; [eapply arr32_frame; [exact Af | intros a Ha; replace a with (f + (a - f)) by lia; apply (KB f (4 * T) (a - f) (ARR f (4 * T) ltac:(cbv [cht_blocks In]; tauto))); rewrite LenF in Ha; lia]|].
split; [eapply arr8_frame; [exact Ak | intros a Ha; replace a with (h + (a - h)) by lia; apply (KB h (3 * T) (a - h) (ARR h (3 * T) ltac:(cbv [cht_blocks In]; tauto))); rewrite LenK in Ha; lia]|].
split; [eapply arr8_frame; [exact Au | intros a Ha; replace a with (u + (a - u)) by lia; apply (KB u T (a - u) (ARR u T ltac:(cbv [cht_blocks In]; tauto))); rewrite LenU in Ha; lia]|].
split; [eapply arr8_frame; [exact Ap | intros a Ha; replace a with (p + (a - p)) by lia; apply (KB p (3 * T) (a - p) (ARR p (3 * T) ltac:(cbv [cht_blocks In]; tauto))); rewrite LenP in Ha; lia]|].
eapply arr32_frame; [exact Ax | intros a Ha; replace a with (x + (a - x)) by lia; apply (KB x (4 * T) (a - x) (ARR x (4 * T) ltac:(cbv [cht_blocks In]; tauto))); rewrite LenX in Ha; lia]. }
intros j Hj k Hk. rewrite Hm; [exact (Hdense j Hj k Hk) | lia | lia | lia]. }
assert (RINVK : forall m, KQ m -> journal ubs2_msyms MR RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac m mdc ->
rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac m mdc).
{ intros m Hm HJm. destruct (KEPT m Hm) as [_ KH].
split; [exact HJm|]. split; [exact Hinit|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc m (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x0 Hx Hlx; apply KH; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros k Hk. apply KH; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
assert (Hfmt34 : 3 <= fmt <= 4) by lia.
change (fmt = 3 \/ fmt = 4) with (boxP (fmt = 3 \/ fmt = 4)) in Hfmt.
change (bef = 0 \/ beffmt = 3 \/ beffmt = 4) with (boxP (bef = 0 \/ beffmt = 3 \/ beffmt = 4)) in Hbef.
assert (Hha01 : 0 <= ha <= 1) by lia. change (ha = 0 \/ ha = 1 /\ fmt = 4) with (boxP (ha = 0 \/ ha = 1 /\ fmt = 4)) in Hha.
set (E := Ereg regs1 (map (Z_to_bv 64) [T; h; u; p; p + 3 * i] ++ [])).
assert (HE : forall n' (rr : reg), Z.of_nat n' = bv_unsigned rr -> ew E n' = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE9 : ew E 9 = Z_to_bv 64 (3 * i)) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE32 : ew E 32 = Z_to_bv 64 T) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 h) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 u) by (subst E; apply (Ereg_vals regs1 _ [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 p) by (subst E; apply (Ereg_vals regs1 _ [] 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (p + 3 * i)) by (subst E; apply (Ereg_vals regs1 _ [] 4%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 5168) by (rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs2segs E ss_Q0b1 (mkst regs1 (Z_to_bv 64 PC_LH) memc (seg_rom ubs2segs))).
{ unfold ss_Q0b1. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
+ apply chunk_ok_val with (v := h); [cbn [sv_denot]; rewrite Z.add_0_r, HE33; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
exact (proj1 (obj_at_nth _ _ _ _ _ 1%nat (8, 8%N) h Hst eq_refl eq_refl)).
+ apply chunk_ok_val with (v := u); [cbn [sv_denot]; rewrite Z.add_0_r, HE34; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
exact (proj1 (obj_at_nth _ _ _ _ _ 2%nat (16, 8%N) u Hst eq_refl eq_refl)).
+ apply chunk_ok_val with (v := p); [cbn [sv_denot]; rewrite Z.add_0_r, HE35; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
exact (proj1 (obj_at_nth _ _ _ _ _ 3%nat (24, 8%N) p Hst eq_refl eq_refl)).
+ apply chunk_ok_val with (v := T); [cbn [sv_denot]; rewrite Z.add_0_r, HE32; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
exact (proj1 (obj_at_nth _ _ _ _ _ 6%nat (44, 4%N) T Hst eq_refl eq_refl)).
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split].
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE9, HU20, HE32, HE35, HE36, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; first [exact Rc16 | subst cnt; lia].
+ cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (U_atom _ 36 _ HE36), (U_atom _ 35 _ HE35) by lia.
split; [|exact I]. apply Bool.negb_true_iff, Z.ltb_ge. lia.
+ cbn [alias_ok]. split; [|exact I]. apply U_inj. rewrite (U_atom _ 36 (p + 3 * i) HE36) by lia. transitivity (3 * i + p); [|lia].
apply U_add_small_q; [rewrite U_and_lit, (U_atom _ 9 (3 * i) HE9) by lia; change (2 ^ 32 - 1) with (Z.ones 32); rewrite Z.land_ones, Z.mod_small by lia; reflexivity
| apply (U_atom _ 35 p HE35); lia | lia | lia | lia]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_LH) memc (seg_rom ubs2segs))) in HJ.
pin_reg' HS (23%bv:reg) (2 ^ 32 - 1) G23.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_col_hash. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (Hmm : ms_mem ms = memc).
{ apply functional_extensionality; intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
clear HF HG.
jreg HS (10%bv:reg) as Ca0. rewrite HE36 in Ca0.
jreg HS (11%bv:reg) as Ca1. rewrite HE33 in Ca1.
jreg HS (12%bv:reg) as Ca2. rewrite HE34 in Ca2.
jreg HS (13%bv:reg) as Ca3. rewrite HE32 in Ca3.
jreg HS (14%bv:reg) as Ca4. jreg HS (1%bv:reg) as Cra.
jreg HS (2%bv:reg) as Csp. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Csp.
cbn [ms_regs mkst] in Ca0, Ca1, Ca2, Ca3, Ca4, Cra, Csp.
assert (Hspz : spZ (ms_regs ms) = sp0 - 5168) by (unfold spZ; rewrite Csp; apply unsigned_lit_small; lia).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. rewrite Hmm. let v := eval vm_compute in ubs2_A_col_hash in change (Z_to_bv 64 v) with (Z_to_bv 64 ubs2_A_col_hash).
rewrite Hmm in HJ.
eapply SR_bind.
{ eapply (COLH RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac memc mdc (ms_regs ms) (p + 3 * i) h u T 3 (ht_used HT) (ht_keys HT) (palc HT i) true hh);
[ exact HJ | rewrite Cra; apply ret_ok_even; vm_compute; reflexivity | rewrite Hspz; exact Hsp16 | rewrite Hspz; lia | rewrite Hspz; lia
| exact Ca0 | exact Ca1 | exact Ca2 | exact Ca3 | exact Ca4
| split; [unfold palc; apply (arr8_col3 ubs2segs memc p (ht_pal HT) i Ap); [lia | rewrite LenP; subst cnt; lia] | left; split; reflexivity]
| exact Au | exact Ak | exact LenU | exact LenK | lia | lia | lia | lia | lia | lia | lia | intros _; exact Hprobe ]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hr10 & Hout3). clear HJ.
rewrite Cra. let v := eval vm_compute in PC_LR in change (Z_to_bv 64 v) with (Z_to_bv 64 PC_LR). cbn [ms_regs mkst] in HP3, Hr10, Hout3. rewrite Hspz in Hout3.
change (if true then hh else 2 ^ 64 - 1) with hh in Hr10.
assert (KQ3 : KQ mem3) by (intros a Ha Hn1 Hn2; apply (Hout3 a Ha Hn1)).
pose proof (proj1 HJ3) as HH3.
pose proof (fun rr Hrr => regs_preserved_frame _ _ HP3 rr Hrr) as RP.
assert (R3 : forall (rr : reg) v, getr regs1 rr = v -> reg_in rr CLOB = false -> sr_get (ss_regs ltac:(lazymatch type of HS with st_ok _ _ ?ssf _ => exact ssf end)) rr = SOff (Z.to_nat (bv_unsigned rr)) 0 -> getr regs3 rr = v).
{ intros rr v Hv Hcl Hsr. rewrite (RP rr ltac:(rewrite Hcl; reflexivity)). pose proof (st_ok_reg ubs2segs E _ _ rr HS) as Q. cbn [ms_regs mkst] in Q. rewrite Hsr in Q.
cbn [sv_denot] in Q. rewrite Z.add_0_r in Q. rewrite Q. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite (HE (Z.to_nat (bv_unsigned rr)) rr) by lia. rewrite Z_to_bv_bv_unsigned. exact Hv. }
pose proof (R3 9%bv _ G9 eq_refl eq_refl) as F9. pose proof (R3 19%bv _ G19 eq_refl eq_refl) as F19. pose proof (R3 22%bv _ G22 eq_refl eq_refl) as F22.
pose proof (R3 24%bv _ G24 eq_refl eq_refl) as F24. pose proof (R3 25%bv _ G25 eq_refl eq_refl) as F25. pose proof (R3 18%bv _ G18 eq_refl eq_refl) as F18.
pose proof (R3 26%bv _ G26 eq_refl eq_refl) as F26. pose proof (R3 27%bv _ G27 eq_refl eq_refl) as F27. pose proof (R3 20%bv _ G20 eq_refl eq_refl) as F20.
pose proof (R3 2%bv _ G2 eq_refl eq_refl) as F2. pose proof (R3 3%bv _ G3 eq_refl eq_refl) as F3. pose proof (R3 4%bv _ G4 eq_refl eq_refl) as F4.
pose proof (R3 8%bv _ G8 eq_refl eq_refl) as F8. pose proof (R3 21%bv _ G21 eq_refl eq_refl) as F21.
assert (F23 : getr regs3 23 = Z_to_bv 64 (2 ^ 32 - 1)).
{ rewrite (RP 23%bv eq_refl). pose proof (st_ok_reg ubs2segs E _ _ 23%bv HS) as Q. cbn [ms_regs mkst] in Q. eval_sr_get_in Q. cbn [sv_denot] in Q. rewrite Q. reflexivity. }
clear R3 RP HS Ca0 Ca1 Ca2 Ca3 Ca4 Cra Csp Hspz.
set (E2 := Ereg regs3 (map (Z_to_bv 64) [f + 4 * hh; fv; f; cnt; p; 2 ^ 64 - 1 - fdp; fdp + 4 * i] ++ [])).
assert (HE2 : forall n' (rr : reg), Z.of_nat n' = bv_unsigned rr -> ew E2 n' = getr regs3 rr) by (intros; subst E2; apply ew_Ereg_nat; assumption).
assert (HE2_32 : ew E2 32 = Z_to_bv 64 (f + 4 * hh)) by (subst E2; apply (Ereg_vals regs3 _ [] 0%nat); reflexivity).
assert (HE2_33 : ew E2 33 = Z_to_bv 64 fv) by (subst E2; apply (Ereg_vals regs3 _ [] 1%nat); reflexivity).
assert (HE2_34 : ew E2 34 = Z_to_bv 64 f) by (subst E2; apply (Ereg_vals regs3 _ [] 2%nat); reflexivity).
assert (HE2_35 : ew E2 35 = Z_to_bv 64 cnt) by (subst E2; apply (Ereg_vals regs3 _ [] 3%nat); reflexivity).
assert (HE2_36 : ew E2 36 = Z_to_bv 64 p) by (subst E2; apply (Ereg_vals regs3 _ [] 4%nat); reflexivity).
assert (HE2_37 : ew E2 37 = Z_to_bv 64 (2 ^ 64 - 1 - fdp)) by (subst E2; apply (Ereg_vals regs3 _ [] 5%nat); reflexivity).
assert (HE2_38 : ew E2 38 = Z_to_bv 64 (fdp + 4 * i)) by (subst E2; apply (Ereg_vals regs3 _ [] 6%nat); reflexivity).
assert (HE2_10 : ew E2 10 = Z_to_bv 64 hh) by (rewrite (HE2 10%nat 10%bv eq_refl); exact Hr10).
assert (HE2_9 : ew E2 9 = Z_to_bv 64 (3 * i)) by (rewrite (HE2 9%nat 9%bv eq_refl); exact F9).
assert (HE2_19 : ew E2 19 = Z_to_bv 64 (4 * i)) by (rewrite (HE2 19%nat 19%bv eq_refl); exact F19).
assert (HE2_22 : ew E2 22 = Z_to_bv 64 i) by (rewrite (HE2 22%nat 22%bv eq_refl); exact F22).
assert (HE2_24 : ew E2 24 = Z_to_bv 64 fdp) by (rewrite (HE2 24%nat 24%bv eq_refl); exact F24).
assert (HU2_2 : bv_unsigned (ew E2 2) = sp0 - 5168) by (rewrite (HE2 2%nat 2%bv eq_refl), F2, Hspv; apply unsigned_lit_small; lia).
assert (HU2_20 : bv_unsigned (ew E2 20) = c) by (rewrite (HE2 20%nat 20%bv eq_refl), F20; apply unsigned_lit_small; lia).
assert (HU2_38 : bv_unsigned (ew E2 38) = fdp + 4 * i) by (rewrite HE2_38; apply unsigned_lit_small; lia).
assert (HU2_32 : bv_unsigned (ew E2 32) = f + 4 * hh) by (rewrite HE2_32; apply unsigned_lit_small; lia).
assert (Hffd : fdp + 4 * cnt <= f \/ f + 4 * T <= fdp) by (apply (Hfdis f (4 * T)); apply ARR; cbv [cht_blocks In]; tauto).
assert (Hfc_sep : c + 48 <= f \/ f + 4 * T <= c).
{ assert (Hp : Permutation (blocks Lc Ac) ((c, CHT_SIZE) :: ((fdp, 4 * cnt) :: (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)])) ++ cht_blocks f h u p x T)).
{ eapply Permutation_trans; [exact Hfd_hd|]. subst KEEP. apply Permutation_sym.
apply (Permutation_middle ((fdp, 4 * cnt) :: (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)])) (cht_blocks f h u p x T) (c, CHT_SIZE)). }
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (c, CHT_SIZE) _ (f, 4 * T) HHc Hp ltac:(apply in_app_iff; right; cbv [cht_blocks In]; tauto)) as X.
cbn [fst snd] in X. rewrite HCHT in X. lia. }
pose proof (Hfdis c CHT_SIZE HcK) as Hcfd. rewrite HCHT in Hcfd.
pose proof (proj1 (obj_at_nth _ _ _ _ _ 0%nat (0, 8%N) f Hst eq_refl eq_refl)) as Vf0.
pose proof (proj1 (obj_at_nth _ _ _ _ _ 3%nat (24, 8%N) p Hst eq_refl eq_refl)) as Vp24.
pose proof (proj1 (obj_at_nth _ _ _ _ _ 5%nat (40, 4%N) cnt Hst eq_refl eq_refl)) as Vc40.
pose proof Hs96 as Sl96. unfold slot, SL_96 in Sl96. rewrite Hspv in Sl96.
assert (HS : st_ok ubs2segs E2 (ss_Q0b2 q0_alias) (mkst regs3 (Z_to_bv 64 PC_LR) mem3 (seg_rom ubs2segs))).
{ unfold ss_Q0b2, q0_alias. subst E2. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
+ rewrite HU2_32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_val with (v := fv); [cbn [sv_denot]; rewrite Z.add_0_r, HE2_33; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
rewrite Z.add_0_r. intros k Hk. rewrite KQ3 by lia. apply Vfv. exact Hk.
+ rewrite HU2_38. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply (present_writable ubs2_msyms). replace (fdp + 4 * i + o) with (fdp + (4 * i + o)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ fdp (4 * cnt) (4 * i + o) HH3 HBfd ltac:(lia))).
+ rewrite HU2_20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* apply chunk_ok_val with (v := f); [cbn [sv_denot]; rewrite Z.add_0_r, HE2_34; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
intros k Hk. rewrite KQ3 by (cbn in Hk; lia). apply Vf0. exact Hk.
* apply chunk_ok_val with (v := p); [cbn [sv_denot]; rewrite Z.add_0_r, HE2_36; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
intros k Hk. rewrite KQ3 by (cbn in Hk; lia). apply Vp24. exact Hk.
* apply chunk_ok_val with (v := cnt); [cbn [sv_denot]; rewrite Z.add_0_r, HE2_35; apply Z_to_bv_bv_unsigned | subst cnt; lia | cbn; lia |].
intros k Hk. rewrite KQ3 by (cbn in Hk; lia). apply Vc40. exact Hk.
+ rewrite HU2_2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply chunk_ok_val with (v := 2 ^ 64 - 1 - fdp); [cbn [sv_denot]; rewrite Z.add_0_r, HE2_37; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
apply (proj2 (val_mem_word_mem ubs2segs _ _ _)). intros k Hk. rewrite KQ3 by lia. apply Sl96. exact Hk.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2_32, HU2_38, HU2_20, HU2_2.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split].
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2_2, HE2_10, HE2_19, HU2_38, HU2_32, HE2_33, HU2_20, HE2_34, HE2_35, HE2_37, !unsigned_lit_small by (subst cnt; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split | |- True => exact I end.
all: first [apply mod4_of16; first [exact Hfd16 | exact Rf16] | exact Rf16 | exact Rc16 | subst cnt; lia].
+ cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (U_atom _ 32 _ HE2_32), (U_atom _ 34 _ HE2_34) by lia.
split; [|exact I]. apply Bool.negb_true_iff, Z.ltb_ge. lia.
+ cbn [alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite (U_atom _ 32 (f + 4 * hh) HE2_32) by lia.
transitivity (hh * 2 ^ 2 + f); [|lia].
apply U_add_small_q; [apply (U_sll_small_q _ _ hh 2); [apply (U_atom _ 10 hh HE2_10); lia | lia | lia | lia] | apply (U_atom _ 34 f HE2_34); lia | lia | lia | lia].
* apply U_inj. rewrite (U_atom _ 38 (fdp + 4 * i) HE2_38) by lia.
apply U_add_small_q; [apply (U_atom _ 24 fdp HE2_24); lia | apply (U_atom _ 19 (4 * i) HE2_19); lia | lia | lia | lia]. }
pin_reg' HS (25%bv:reg) 0 F25.
assert (Wfd : wtok' RGBA_STK sp0 (FPfoot r g bef beffmt s N) (blocks L A) (fdp, 4 * cnt)).
{ intros blc k Hbin Hk. right. right. exists fdp, (4 * cnt). split; [exact Hbin|]. split; [exact Hfd_tmp | cbn [fst snd] in Hk |- *; lia]. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PC_LR) mem3 (seg_rom ubs2segs))) in HJ3.
jrun LAWS ubs2tbl_ok HS HJ3.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 38); [reflexivity | ew_havoc; exact HU2_38 | cbn [r_wlo r_whi]; intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ _ (4 * cnt)); [exact Wfd | exact HBfd | lia] | apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HG.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KQ4 : KQ (ms_mem msx)) by (intros a Ha Hn1 Hn2; rewrite <- (KQ3 a Ha Hn1 Hn2); mb_frame_g HF; [reflexivity | rewrite HU2_32; lia | rewrite HU2_38; lia | rewrite HU2_20; lia | rewrite HU2_2; lia]);
pose proof (mem_grows_trans _ _ _ ltac:(exact (fun x Hx => Hx)) HG) as HGA
end.
clear HF HG.
Ltac tail_facts HS HF HG HGA KQ4 HU2_32 HU2_38 HU2_20 HU2_2 HE2_33 Hfv Hdense LAWS HH3 HBfd fdp cnt i fv ent KQ5 PRES5 DENSE5 :=
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KQ5 : forall a, 0 <= a < 2 ^ 64 -> ~ (_ <= a < _) -> ~ (fdp + 4 * i <= a < fdp + 4 * i + 4) -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs _ a)
by (intros a Ha Hn1 Hn2; rewrite <- (KQ4 a Ha Hn1 Hn2); mb_frame_g HF; [reflexivity | rewrite HU2_32; lia | rewrite HU2_38; lia | rewrite HU2_20; lia | rewrite HU2_2; lia]);
assert (PRES5 : forall k, 0 <= k < 4 * cnt -> exists b, mbyte ubs2segs (ms_mem msx) (fdp + k) = Some b)
by (intros k Hk; apply (present_mbyte ubs2_msyms); eapply (present_grows _ _ _ HG); eapply (present_grows _ _ _ HGA); apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ fdp (4 * cnt) k HH3 HBfd Hk)));
assert (DENSE5 : forall j, 0 <= j < i + 1 -> val_mem ubs2segs (ms_mem msx) (fdp + 4 * j) 4 (getz (map snd ent) j))
by (intros j Hj; destruct (Z.eq_dec j i) as [->|Hne];
[ rewrite Hfv; replace (fdp + 4 * i) with (fdp + 4 * i + 0) by lia;
eapply (st_chunk_val ubs2segs _ _ _ 1%nat _ 38%nat 0 4%N (SOff 33 0) (fdp + 4 * i) fv HS eq_refl eq_refl); [cbv; tauto | ew_havoc; exact HU2_38 | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE2_33 | lia | cbn; lia]
| intros k Hk; rewrite KQ5 by lia; apply (Hdense j ltac:(lia) k Hk) ]);
clear HF HG
end.
jbranch ubs2tbl HS.
-
rewrite branch_ltu_U, (U_atom_off _ 22 i 1 HE2_22), (U_atom _ 35 cnt HE2_35) in Hc by (subst cnt; lia).
assert (Hlt : i + 1 < cnt) by (apply Z.ltb_lt in Hc; exact Hc). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_LH.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 38); [reflexivity | ew_havoc; exact HU2_38 | cbn [r_wlo r_whi]; intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ _ (4 * cnt)); [exact Wfd | exact HBfd | lia] | apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HG |- *.
tail_facts HS HF HG HGA KQ4 HU2_32 HU2_38 HU2_20 HU2_2 HE2_33 Hfv Hdense LAWS HH3 HBfd fdp cnt i fv ent KQ5 PRES5 DENSE5.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. let v := eval vm_compute in PC_LH in change (Z_to_bv 64 v) with (Z_to_bv 64 PC_LH).
lazymatch goal with |- SR _ (mkCfg (mkst ?regsF _ ?memF _) _) _ =>
apply (IH (i + 1) regsF Lc Ac memF mdc ha pnew fimg imgl (mkCHT c f h u p x T hS uS TS HT ent) fdp); [cbn [ch_H]; subst cnt; lia|] end.
unfold at_LH. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
destruct (TRANS _ KQ5 (or_intror I)) as (Tslm & Tslq & Ts96 & Tfc & Tobj & Tcg & Timg & Tst & Tarr & _).
split; [exact (RINVK _ KQ5 HJ3)|].
split. { split; [jreg HS (2%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 2%nat 2%bv eq_refl); exact F2|].
split; [jreg HS (3%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 3%nat 3%bv eq_refl); exact F3|].
jreg HS (4%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 4%nat 4%bv eq_refl); exact F4. }
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|]. split; [exact Hc256|]. split; [subst cnt; lia|].
split; [jreg HS (9%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, HE2_9, unsigned_lit_small by lia; f_equal; lia|].
split; [jreg HS (19%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, HE2_19, unsigned_lit_small by lia; f_equal; lia|].
split; [jreg HS (22%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, HE2_22, unsigned_lit_small by lia; f_equal; lia|].
split; [jreg HS (23%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 23%nat 23%bv eq_refl); exact F23|].
split; [jreg HS (24%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 24%nat 24%bv eq_refl); exact F24|].
split; [jreg HS (25%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; reflexivity|].
split; [jreg HS (18%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 18%nat 18%bv eq_refl); exact F18|].
split; [jreg HS (26%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 26%nat 26%bv eq_refl); exact F26|].
split; [jreg HS (27%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 27%nat 27%bv eq_refl); exact F27|].
split; [jreg HS (20%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 20%nat 20%bv eq_refl); exact F20|].
split; [jreg HS (8%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 8%nat 8%bv eq_refl); exact F8|].
split; [jreg HS (21%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 21%nat 21%bv eq_refl); exact F21|].
split; [exact Tslm|]. split; [exact Tslq|]. split; [exact Ts96|]. split; [exact Tfc|]. split; [exact Tobj|]. split; [exact Tcg|]. split; [exact Timg|].
split; [exact Tst|]. split; [exact Tarr|]. split; [exact Hinv|]. split; [exact HTT|]. split; [exact Hts|]. split; [exact Hsum|].
split; [exact DENSE5|]. split; [exact PRES5|].
split; [exact Hpnz|]. split; [exact Hfnz|]. split; [exact Hfdnz|]. split; [exact Hfd16|]. exact HB.
-
rewrite branch_ltu_U, (U_atom_off _ 22 i 1 HE2_22), (U_atom _ 35 cnt HE2_35) in Hc by (subst cnt; lia).
assert (Heq : i + 1 = cnt) by (apply Z.ltb_ge in Hc; subst cnt; lia). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_CR.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 38); [reflexivity | ew_havoc; exact HU2_38 | cbn [r_wlo r_whi]; intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ _ (4 * cnt)); [exact Wfd | exact HBfd | lia] | apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HG |- *.
tail_facts HS HF HG HGA KQ4 HU2_32 HU2_38 HU2_20 HU2_2 HE2_33 Hfv Hdense LAWS HH3 HBfd fdp cnt i fv ent KQ5 PRES5 DENSE5.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. let v := eval vm_compute in PC_CR in change (Z_to_bv 64 v) with (Z_to_bv 64 PC_CR).
lazymatch goal with |- SR _ (mkCfg (mkst ?regsF _ ?memF _) _) _ =>
apply (KCR fx regsF Lc Ac memF mdc ha pnew fimg imgl (mkCHT c f h u p x T hS uS TS HT ent) cnt fdp (map snd ent) (ht_pal HT) Hfrm0) end.
unfold at_CR, chtq_ok, dense_ok. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
destruct (TRANS _ KQ5 (or_intror I)) as (Tslm & Tslq & Ts96 & Tfc & Tobj & Tcg & Timg & Tst & Tarr & _).
split; [exact (RINVK _ KQ5 HJ3)|].
split. { split; [jreg HS (2%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 2%nat 2%bv eq_refl); exact F2|].
split; [jreg HS (3%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 3%nat 3%bv eq_refl); exact F3|].
jreg HS (4%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 4%nat 4%bv eq_refl); exact F4. }
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|].
split; [jreg HS (14%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, HE2_35, unsigned_lit_small by (subst cnt; lia); f_equal; lia|].
split; [jreg HS (25%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE2_36|].
split; [jreg HS (24%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 24%nat 24%bv eq_refl); exact F24|].
split; [jreg HS (20%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 20%nat 20%bv eq_refl); exact F20|].
split; [jreg HS (18%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 18%nat 18%bv eq_refl); exact F18|].
split; [jreg HS (27%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 27%nat 27%bv eq_refl); exact F27|].
split; [jreg HS (8%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 8%nat 8%bv eq_refl); exact F8|].
split; [jreg HS (21%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE2 21%nat 21%bv eq_refl); exact F21|].
split; [exact Tslm|]. split; [exact Tslq|]. split; [exact Ts96|]. split; [exact Tfc|]. split; [exact Tobj|]. split; [exact Tcg|]. split; [exact Timg|].
split. { split; [exact Tst|]. split; [exact (proj1 (proj2 (proj2 (proj2 Tarr))))|]. split; [exact LenP|]. split; [exact Hts|].
intros b Hb. unfold cht_blks in Hb. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T] in Hb.
destruct Hb as [<-|Hb]; [cbn [fst]; lia|].
destruct b as [b m]. cbn [fst]. exact (proj1 (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ (ARR b m Hb)))). }
split. {
pose proof (inv_cnt HT ent Hinv) as [Hel _].
split. { intros j Hj. rewrite length_map in Hj.
pose proof (DENSE5 (Z.of_nat j) ltac:(unfold elen in Hel; subst cnt; lia)) as Hv. unfold getz in Hv. rewrite Nat2Z.id in Hv.
assert (Hjn : nth_error ent j <> None) by (apply nth_error_Some; lia).
destruct (nth_error ent j) as [[cj fj]|] eqn:Ej; [|congruence].
pose proof (zsum_pos_le ent j _ _ (ent_freq_pos HT ent Hinv) Ej) as Hle.
pose proof (proj1 (Forall_forall _ _) (ent_freq_pos HT ent Hinv) (cj, fj) (nth_error_In _ _ Ej)) as Hge. cbn [snd] in Hge.
rewrite (nth_error_nth (map snd ent) j 0 ltac:(rewrite nth_error_map, Ej; reflexivity) : nth j (map snd ent) 0 = fj) in Hv |- *.
split; [exact Hv | lia]. }
split; [unfold zlen; rewrite length_map; unfold elen in Hel; subst cnt; lia|].
split; [exact Hc256|]. split; [rewrite LenP; subst cnt; lia|].
split. { intros j Hj. assert (Hjn : nth_error ent (Z.to_nat j) <> None) by (apply nth_error_Some; unfold elen in Hel; subst cnt; lia).
destruct (nth_error ent (Z.to_nat j)) as [[cj fj]|] eqn:Ej; [|congruence].
pose proof (proj1 (Forall_forall _ _) (ent_freq_pos HT ent Hinv) (cj, fj) (nth_error_In _ _ Ej)) as Hge. cbn [snd] in Hge.
unfold getz. rewrite (nth_error_nth (map snd ent) (Z.to_nat j) 0 ltac:(rewrite nth_error_map, Ej; reflexivity) : nth (Z.to_nat j) (map snd ent) 0 = fj). exact Hge. }
split; [exact Hsum|].
intros j j' Hj Hj' Hne Heqc. apply Hne.
destruct (ent_slot HT ent Hinv j ltac:(subst cnt; lia)) as (hj & _ & _ & Ej & Pj & _).
destruct (ent_slot HT ent Hinv j' ltac:(subst cnt; lia)) as (hj' & _ & _ & Ej' & Pj' & _).
unfold palc in Pj, Pj'. rewrite <- Pj in Ej. rewrite <- Pj', <- Heqc in Ej'.
exact (ent_distinct HT ent Hinv j j' _ _ _ Ej Ej' ltac:(lia) ltac:(lia)). }
split; [exact Hpnz|]. split; [exact Hfnz|]. split; [exact Hfdnz|]. exact HB.
Qed.
Lemma LH_all : K_CR API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
forall n i, K_LHn n i.
Proof. intros KCR n. induction n as [|n IHn]; [apply LH_base | intros i; apply (LH_body n i KCR IHn)]. Qed.
Lemma ubs2_rgbadd_Q0b :
K_CR API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_LH API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest 0.
Proof.
intros KCR regs1 Lc Ac memc mdc ha pnew fimg imgl C fdp HAT.
apply (LH_all KCR (Z.to_nat (ht_cnt (ch_H C))) 0 regs1 Lc Ac memc mdc ha pnew fimg imgl C fdp); [| exact HAT].
destruct HAT as (_ & _ & _ & _ & _ & _ & Hi & _). rewrite Z2Nat.id by lia. lia.
Qed.
Theorem ubs2_rgbadd_Q0 : seg_Q0 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KSM KCR KXC.
exact (ubs2_rgbadd_Q0a API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
(ubs2_rgbadd_Q0b KCR) KSM KXC).
Qed.
End e.
End d.
