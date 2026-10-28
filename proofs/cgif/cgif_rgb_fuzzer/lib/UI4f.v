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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g UI3h UI3d
UI4v UI46 UI4g UI4c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma obj_at_cht_set_ts : forall (m m' : word -> option byte) c v0 v1 v2 v3 v4 v5 v6 v6',
obj_at ubs2segs m c LAY_Cht [v0; v1; v2; v3; v4; v5; v6] ->
(forall a, c <= a < c + 48 -> ~ (c + 44 <= a < c + 48) -> mbyte ubs2segs m' a = mbyte ubs2segs m a) ->
val_mem ubs2segs m' (c + 44) 4 v6' -> 0 <= v6' < 2 ^ 32 ->
obj_at ubs2segs m' c LAY_Cht [v0; v1; v2; v3; v4; v5; v6'].
Proof.
intros m m' c v0 v1 v2 v3 v4 v5 v6 v6' Hobj KEEP Hv Hr.
cbn [obj_at LAY_Cht] in Hobj |- *. unfold field_ok in *. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hobj |- *.
destruct Hobj as ([A0 B0] & [A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6] & _).
assert (K : forall off n v, val_mem ubs2segs m (c + off) n v -> 0 <= off -> off + Z.of_nat n <= 44 -> val_mem ubs2segs m' (c + off) n v).
{ intros off n v Hvm H0 H1. apply (val_mem_kept m); [exact Hvm|]. intros k Hk. apply KEEP; lia. }
split; [split; [apply K; [exact A0 | lia | cbn; lia] | exact B0]|].
split; [split; [apply K; [exact A1 | lia | cbn; lia] | exact B1]|].
split; [split; [apply K; [exact A2 | lia | cbn; lia] | exact B2]|].
split; [split; [apply K; [exact A3 | lia | cbn; lia] | exact B3]|].
split; [split; [apply K; [exact A4 | lia | cbn; lia] | exact B4]|].
split; [split; [apply K; [exact A5 | lia | cbn; lia] | exact B5]|].
split; [split; [exact Hv | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hr]|]. exact I.
Qed.
Lemma obj_at_cht_set_fhu : forall (m m' : word -> option byte) c v0 v1 v2 v3 v4 v5 v6 v0' v1' v2',
obj_at ubs2segs m c LAY_Cht [v0; v1; v2; v3; v4; v5; v6] ->
(forall a, c <= a < c + 48 -> ~ (c <= a < c + 24) -> mbyte ubs2segs m' a = mbyte ubs2segs m a) ->
val_mem ubs2segs m' c 8 v0' -> val_mem ubs2segs m' (c + 8) 8 v1' -> val_mem ubs2segs m' (c + 16) 8 v2' ->
0 <= v0' < 2 ^ 64 -> 0 <= v1' < 2 ^ 64 -> 0 <= v2' < 2 ^ 64 ->
obj_at ubs2segs m' c LAY_Cht [v0'; v1'; v2'; v3; v4; v5; v6].
Proof.
intros m m' c v0 v1 v2 v3 v4 v5 v6 v0' v1' v2' Hobj KEEP H0 H1 H2 R0 R1 R2.
cbn [obj_at LAY_Cht] in Hobj |- *. unfold field_ok in *. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hobj |- *.
destruct Hobj as ([A0 B0] & [A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6] & _).
assert (K : forall off n v, val_mem ubs2segs m (c + off) n v -> 24 <= off -> off + Z.of_nat n <= 48 -> val_mem ubs2segs m' (c + off) n v).
{ intros off n v Hvm Ha Hb. apply (val_mem_kept m); [exact Hvm|]. intros k Hk. apply KEEP; lia. }
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
split; [split; [rewrite Z.add_0_r; exact H0 | exact R0]|].
split; [split; [exact H1 | exact R1]|].
split; [split; [exact H2 | exact R2]|].
split; [split; [apply K; [exact A3 | lia | cbn; lia] | exact B3]|].
split; [split; [apply K; [exact A4 | lia | cbn; lia] | exact B4]|].
split; [split; [apply K; [exact A5 | lia | cbn; lia] | exact B5]|].
split; [split; [apply K; [exact A6 | lia | cbn; lia] | exact B6]|]. exact I.
Qed.
Section e.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation RINV := (rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Local Notation AT_POST := (at_POST API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_P1 := (at_P1 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_P2 := (at_P2 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_P3 := (at_P3 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_INC := (at_INC API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation POST_MEM := (post_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation KEEPB := (keepb r g bef beffmt s N img fmt rest).
Local Notation RINV_CALL := (rgba_inv_call API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Lemma post_mem_kept : forall Lc Ac (memc memX : word -> option byte) mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K (l : list (Z * Z)),
heap_ok MR Lc Ac memc mdc -> alloc_ceiling <= SP -> SP + RGBA_FRAME <= 2 ^ 63 -> (fmt = 3 \/ fmt = 4) ->
Permutation (blocks Lc Ac) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ l) -> (forall b, In b (newb T' p1 x1 h1 u1 f1) -> In b l) ->
POST_MEM memc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) ->
(forall b n k, In (b, n) (BASE0 ++ newb T' p1 x1 h1 u1 f1) -> 0 <= k < n -> mbyte ubs2segs memX (b + k) = mbyte ubs2segs memc (b + k)) ->
POST_MEM memX i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K.
Proof.
intros Lc Ac memc memX mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K l HH Hsp Hsp2 Hfmt HB Hsub
(Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & S72 & Hfc & Hobj & Hcg & [Himg Hlen] & Hpn & Hfi & (Af & Ah & Au & Ap & Ax) & HTK & Hch' & HK & Hinv & HT & Hch & R1 & R2 & R3 & EhS & EuS & Hz) KH KB.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof HK as ((M1 & M2 & M3 & M4 & M5) & _). rewrite HTK in M1, M2, M3, M4, M5.
assert (KS : forall off v, 0 <= off -> off + 8 <= RGBA_FRAME -> slot regs0 memc off v -> slot regs0 memX off v).
{ intros off v H0 H1 Hs. unfold slot in *. apply (val_mem_kept8 memc); [exact Hs|]. intros k Hk. apply KH; lia. }
assert (KB0 : forall y k, In y BASE0 -> 0 <= k < snd y -> mbyte ubs2segs memX (fst y + k) = mbyte ubs2segs memc (fst y + k)).
{ intros [b n] k Hy Hk. apply (KB b n k); [apply in_app_iff; left; exact Hy | exact Hk]. }
assert (KBn : forall b n a, In (b, n) (newb T' p1 x1 h1 u1 f1) -> b <= a < b + n -> mbyte ubs2segs memX a = mbyte ubs2segs memc a).
{ intros b n a Hb Ha. replace a with (b + (a - b)) by lia. apply (KB b n (a - b)); [apply in_app_iff; right; exact Hb | lia]. }
unfold post_mem. destruct Hslots as (M8 & M16 & M24 & M48).
split. { unfold slots_mid, SL_N, SL_cfp, SL_new, SL_fimg in *. repeat split; (apply KS; [lia | lia | assumption]). }
split; [apply KS; unfold SL_32 in *; [lia | lia | exact S32]|].
split; [apply KS; unfold SL_40 in *; [lia | lia | exact S40]|].
split; [apply KS; unfold SL_56 in *; [lia | lia | exact S56]|].
split; [apply KS; unfold SL_64 in *; [lia | lia | exact S64]|].
split; [apply KS; unfold SL_80 in *; [lia | lia | exact S80]|].
split; [apply KS; unfold SL_112 in *; [lia | lia | exact S112]|].
split; [apply KS; unfold SL_120 in *; [lia | lia | exact S120]|].
split; [apply KS; unfold SL_72 in *; [lia | lia | exact S72]|].
split. { unfold fcfg_at in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 29); [exact Hfc | reflexivity |]. intros k Hk. unfold OFF_fcfg. apply KH; lia. }
split. { unfold rgb_obj in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros k Hk. apply (KB0 (r, RGB_SIZE) k); [left; reflexivity | cbn; exact Hk]. }
split. { eapply (cgif_at_kept _ _ g s N (cgif_blocks g s N) []); [rewrite app_nil_r; apply Permutation_refl | exact Hcg |].
intros b n k Hbn Hk. apply (KB0 (b, n) k); [| cbn; exact Hk]. right. apply in_app_iff. left. exact Hbn. }
split. { split; [|exact Hlen]. eapply arr8_frame; [exact Himg|]. intros a Ha. replace a with (img + (a - img)) by lia. apply (KB0 (img, fmt * N) (a - img)); [| cbn [snd]; clear - Ha Hlen; lia].
right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. unfold img_block, fmt_okb. destruct Hfmt as [-> | ->]; left; reflexivity. }
split; [exact Hpn|]. split; [exact Hfi|].
split. { unfold cht_arrays. split; [|split; [|split; [|split]]].
- eapply arr32_frame; [exact Af|]. intros a Ha. apply (KBn f1 (4 * T')); [cbn; auto 10 | rewrite <- M3; lia].
- eapply arr8_frame; [exact Ah|]. intros a Ha. apply (KBn h1 (3 * T')); [cbn; auto 10 | rewrite <- M2; lia].
- eapply arr8_frame; [exact Au|]. intros a Ha. apply (KBn u1 T'); [cbn; auto 10 | rewrite <- M1; lia].
- eapply arr8_frame; [exact Ap|]. intros a Ha. apply (KBn p1 (3 * T')); [cbn; auto 10 | rewrite <- M5; lia].
- eapply arr32_frame; [exact Ax|]. intros a Ha. apply (KBn x1 (4 * T')); [cbn; auto 10 | rewrite <- M4; lia]. }
split; [exact HTK|]. split; [exact Hch'|]. split; [exact HK|]. split; [exact Hinv|]. split; [exact HT|]. split; [exact Hch|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact EhS|]. split; [exact EuS | exact Hz].
Qed.
Section f.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc, AT_P1 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_P1) memc (seg_rom ubs2segs)) mdc) POST.
Definition ss_POST : sstate := mkSS PC_POST sr_atoms [YQ0b.mkRegion (Some 20%nat) 0 48 44 48 [mkChunk 8 (CVal 8 (SOff 32%nat 0))]] None (mkFacts [(18%nat, mkAF 521 (2^24) 0)] [] []).
Theorem POST_stretch : forall regs1 Lc Ac memc mdc, AT_POST regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_POST) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G24 & G25 & G18 & G26 & G20 & G9 & G8 & G21) & HK & LM & RZB).
pose proof LM as (RZM & S72 & CS & HCA & HTK & PS).
pose proof RZM as (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & Hfc & Hobj & Hcg & Himg & Hpn & Hfi & Bf & Bh & Bu & Hinv & HT & Hch & HTlt & RhS & RuS & RTS & EhS & EuS & ETS & Hz).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
unfold rz_blocks, keepb in RZB. rewrite <- !app_assoc in RZB.
set (T := ch_T C) in *.
assert (PM : POST_MEM memc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K).
{ unfold post_mem. repeat (split; [assumption|]). exact Hz. }
assert (INB : forall b, In b (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]).
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (Q0 & Q1 & _). lia. }
destruct (RNG (ch_h C) (3 * T) ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; cbn; auto 10) ltac:(lia)) as [Rh0 Rh1].
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
assert (SEPc : forall y, In y (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) -> ch_c C + 48 <= fst y \/ fst y + snd y <= ch_c C).
{ intros y Hy. pose proof (perm_sep API Lc Ac memc mdc (ch_c C, CHT_SIZE) y (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ([(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X. apply X; [rewrite <- !app_assoc; exact RZB | rewrite <- app_assoc; exact Hy]. }
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 1 _ _ PS eq_refl eq_refl) as [B1s _]. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in B1s. rewrite EhS in B1s.
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_h C] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_h C)) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HE18 : ew E 18 = Z_to_bv 64 T') by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E ss_POST (mkst regs1 (Z_to_bv 64 PC_POST) memc (seg_rom ubs2segs))).
{ unfold ss_POST. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|].
split. { intros o Ho. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE o HHc ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity) ltac:(unfold CHT_SIZE; lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_h C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B1s.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE18, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_POST) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ eapply wr_ok_cons_gen; [reflexivity | exact HU20 | cbn [r_wlo r_whi]; intros a Ha |]; [| apply wr_ok_nil].
apply (wr_byte_tmp API L A regs0 r g bef beffmt s N img fmt rest Lc Ac memc mdc ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) (ch_c C) CHT_SIZE a HHc);
[exact RZB | exact HB0 | apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | unfold CHT_SIZE; lia | unfold CHT_SIZE; lia]. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (ch_c C + 44 <= a < ch_c C + 48) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hn. mb_frame_g HF; [reflexivity | rewrite HU20; exact Hn]. }
assert (V44 : val_mem ubs2segs (ms_mem ms) (ch_c C + 44) 4 T').
{ apply (st_chunk_val_g E _ _ 0%nat _ 20%nat 44 4%N (SOff 18 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU20 | cbn [sv_denot]; rewrite Z.add_0_r, HE18, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
assert (Ma0 : getr (ms_regs ms) 10 = Z_to_bv 64 (ch_h C)) by (jreg HS (10%bv:reg) as Hq; rewrite Hq, HE32; reflexivity).
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 24; 25; 18; 26; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
assert (HBq : Permutation (blocks Lc Ac) (optb (ch_h C) (3 * T) ++ (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1))).
{ eapply Permutation_trans; [exact RZB|]. unfold optb. destruct (Z.eqb_spec (ch_h C) 0); [lia|]. perm_tac. }
assert (HFPq : ch_h C <> 0 -> In (ch_h C, 3 * T) (blocks L A) -> forall i0, 0 <= i0 < 3 * T -> inFP (FPfoot r g bef beffmt s N) (ch_h C + i0)).
{ intros Hnz Hin0 i0 Hi0. exfalso.
apply (tmp_not_entry API L A Lc Ac memc mdc (ch_h C, 3 * T) BASE0 ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc RZB HB0); [| cbn; lia | exact Hin0].
apply in_app_iff. right. apply in_app_iff. left. cbn. auto 10. }
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API)) with (p := ch_h C) (n := 3 * T) (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact HBq | exact Ma0
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity | exact HFPq ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, HB2, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. rewrite (proj1 (Hhi2 a Ha ltac:(lia))). apply K1; lia. }
assert (KB2 : forall b m k, In (b, m) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_f C, 4 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) -> 0 <= k < m -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b m k Hb Hk.
assert (Hb2 : In (b, m) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1)).
{ apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
rewrite (Hkeep2 b m k); [| eapply Permutation_in; [apply Permutation_sym; exact HB2 | exact Hb2] | exact Hk].
assert (Hb3 : In (b, m) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1)).
{ apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right].
cbn [app In] in Hb |- *. destruct Hb as [Hb|[Hb|Hb]]; auto. }
pose proof (SEPc (b, m) Hb3) as X. cbn [fst snd] in X.
destruct (RNG b m ltac:(apply INB; apply in_app_iff in Hb3; apply in_app_iff; destruct Hb3 as [Hb3|Hb3]; [left; exact Hb3 | right]; apply in_app_iff in Hb3; apply in_app_iff; destruct Hb3 as [Hb3|Hb3]; [left; exact Hb3 | right; right; exact Hb3]) ltac:(lia)) as [Rb0 Rb1].
apply K1; lia. }
assert (KC2 : forall a, ch_c C <= a < ch_c C + 48 -> mbyte ubs2segs mem2 a = mbyte ubs2segs (ms_mem ms) a).
{ intros a Ha. replace a with (ch_c C + (a - ch_c C)) by lia. apply (Hkeep2 (ch_c C) CHT_SIZE (a - ch_c C)); [| unfold CHT_SIZE; lia].
eapply Permutation_in; [apply Permutation_sym; exact HB2|]. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
change (Z_to_bv 64 81276) with (Z_to_bv 64 PC_P1). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2). unfold at_P1.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [exact HRZF|].
split. { unfold s_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)),
(GK 18%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split. { apply (post_mem_kept Lc Ac memc mem2 mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ([(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB ltac:(intros b Hb; apply in_app_iff; right; exact Hb) PM).
- intros a Ha Hs. apply KH2; [exact Ha | exact Hs].
- intros b m k Hb Hk. apply (KB2 b m k); [| exact Hk]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_app_iff; right; apply in_app_iff; right; exact Hb]. }
split. { unfold p_struct. rewrite <- ETS in RT1, RT2. apply (obj_at_cht_set_ts memc mem2 (ch_c C) _ _ _ _ _ _ _ T' PS); [| | lia].
- intros a Ha Hna. rewrite (KC2 a Ha). apply K1; lia.
- apply (val_mem_kept (ms_mem ms)); [exact V44|]. intros k Hk. apply KC2. lia. }
exact HB2.
Qed.
End f.
Section h.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc, AT_P2 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_P2) memc (seg_rom ubs2segs)) mdc) POST.
Definition ss_P1 : sstate := mkSS PC_P1 sr_atoms [YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 16 (CVal 8 (SOff 32%nat 0))]] None (mkFacts [] [] []).
Theorem P1_stretch : forall regs1 Lc Ac memc mdc, AT_P1 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_P1) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G24 & G25 & G18 & G26 & G20 & G9 & G8 & G21) & PM & PS & RZB).
pose proof PM as (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & S72 & Hfc & Hobj & Hcg & Himg & Hpn & Hfi & HCA & HTK & Hch' & HK & Hinv & HT & Hch & RhS & RuS & RTS & EhS & EuS & Hz).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof Hinv as ((L1 & _) & (C1 & _) & _). pose proof (ts_chain_ok _ Hch') as (RT1' & RT2' & RT3').
set (T := ch_T C) in *.
assert (INB : forall b, In b (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]).
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (Q0 & Q1 & _). lia. }
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). assert (HTpos : 0 < T) by lia.
destruct (RNG (ch_u C) T ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; cbn; auto 10) HTpos) as [Rh0 Rh1].
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_u C] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_u C)) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 2 _ _ PS eq_refl eq_refl) as [B2s _]. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in B2s. rewrite EuS in B2s.
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E ss_P1 (mkst regs1 (Z_to_bv 64 PC_P1) memc (seg_rom ubs2segs))).
{ unfold ss_P1. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_u C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B2s.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- exact I. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_P1) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x) end).
assert (Ma0 : getr (ms_regs ms) 10 = Z_to_bv 64 (ch_u C)) by (jreg HS (10%bv:reg) as Hq; rewrite Hq, HE32; reflexivity).
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 24; 25; 18; 26; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
assert (HBq : Permutation (blocks Lc Ac) (optb (ch_u C) T ++ (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T)] ++ newb T' p1 x1 h1 u1 f1))).
{ eapply Permutation_trans; [exact RZB|]. unfold optb. destruct (Z.eqb_spec (ch_u C) 0); [lia|]. perm_tac. }
assert (HFPq : ch_u C <> 0 -> In (ch_u C, T) (blocks L A) -> forall i0, 0 <= i0 < T -> inFP (FPfoot r g bef beffmt s N) (ch_u C + i0)).
{ intros Hnz Hin0 i0 Hi0. exfalso.
apply (tmp_not_entry API L A Lc Ac memc mdc (ch_u C, T) BASE0 ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc RZB HB0); [| cbn; lia | exact Hin0].
apply in_app_iff. right. apply in_app_iff. left. cbn. auto 10. }
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API)) with (p := ch_u C) (n := T) (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact HBq | exact Ma0
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity | exact HFPq ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, HB2, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b m k, In (b, m) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T)] ++ newb T' p1 x1 h1 u1 f1) -> 0 <= k < m -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b m k Hb Hk. apply (Hkeep2 b m k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact HB2 | exact Hb]. }
change (Z_to_bv 64 81284) with (Z_to_bv 64 PC_P2). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2). unfold at_P2.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [exact HRZF|].
split. { unfold s_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)),
(GK 18%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split. { apply (post_mem_kept Lc Ac memc mem2 mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ([(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB ltac:(intros b Hb; apply in_app_iff; right; exact Hb) PM).
- intros a Ha Hs. apply KH2; [exact Ha | exact Hs].
- intros b m k Hb Hk. apply (KB2 b m k); [| exact Hk]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_app_iff; right; apply in_app_iff; right; exact Hb]. }
split. { unfold p_struct. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact PS | reflexivity |]. intros k Hk. apply (KB2 (ch_c C) CHT_SIZE k); [| exact Hk].
apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
exact HB2.
Qed.
End h.
Section j.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc, AT_P3 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_P3) memc (seg_rom ubs2segs)) mdc) POST.
Definition ss_P2 : sstate := mkSS PC_P2 sr_atoms [YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 0 (CVal 8 (SOff 32%nat 0))]] None (mkFacts [] [] []).
Theorem P2_stretch : forall regs1 Lc Ac memc mdc, AT_P2 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_P2) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G24 & G25 & G18 & G26 & G20 & G9 & G8 & G21) & PM & PS & RZB).
pose proof PM as (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & S72 & Hfc & Hobj & Hcg & Himg & Hpn & Hfi & HCA & HTK & Hch' & HK & Hinv & HT & Hch & RhS & RuS & RTS & EhS & EuS & Hz).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof Hinv as ((L1 & _) & (C1 & _) & _). pose proof (ts_chain_ok _ Hch') as (RT1' & RT2' & RT3').
pose proof Hslots as (M8 & M16 & M24 & M48).
set (T := ch_T C) in *.
assert (INB : forall b, In b (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T)] ++ newb T' p1 x1 h1 u1 f1) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]).
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (Q0 & Q1 & _). lia. }
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). assert (HTpos : 0 < T) by lia.
destruct (RNG (ch_f C) (4 * T) ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; cbn; auto 10) ltac:(lia)) as [Rh0 Rh1].
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; cbn; auto 10) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 0 _ _ PS eq_refl eq_refl) as [Bc0 _]. cbn [fst snd] in Bc0. change (N.to_nat 8) with 8%nat in Bc0. rewrite Z.add_0_r in Bc0.
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_f C] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_f C)) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E ss_P2 (mkst regs1 (Z_to_bv 64 PC_P2) memc (seg_rom ubs2segs))).
{ unfold ss_P2. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HU20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_f C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact Bc0.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- exact I. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_P2) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x) end).
assert (Ma0 : getr (ms_regs ms) 10 = Z_to_bv 64 (ch_f C)) by (jreg HS (10%bv:reg) as Hq; rewrite Hq; exact HE32).
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 24; 25; 18; 26; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
assert (HBq : Permutation (blocks Lc Ac) (optb (ch_f C) (4 * T) ++ (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE)] ++ newb T' p1 x1 h1 u1 f1))).
{ eapply Permutation_trans; [exact RZB|]. unfold optb. destruct (Z.eqb_spec (ch_f C) 0); [lia|]. perm_tac. }
assert (HFPq : ch_f C <> 0 -> In (ch_f C, 4 * T) (blocks L A) -> forall i0, 0 <= i0 < 4 * T -> inFP (FPfoot r g bef beffmt s N) (ch_f C + i0)).
{ intros Hnz Hin0 i0 Hi0. exfalso.
apply (tmp_not_entry API L A Lc Ac memc mdc (ch_f C, 4 * T) BASE0 ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T)] ++ newb T' p1 x1 h1 u1 f1) HHc RZB HB0); [| cbn; lia | exact Hin0].
apply in_app_iff. right. apply in_app_iff. left. cbn. auto 10. }
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API)) with (p := ch_f C) (n := 4 * T) (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact HBq | exact Ma0
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity | exact HFPq ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, HB2, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b m k, In (b, m) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE)] ++ newb T' p1 x1 h1 u1 f1) -> 0 <= k < m -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b m k Hb Hk. apply (Hkeep2 b m k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact HB2 | exact Hb]. }
change (Z_to_bv 64 81292) with (Z_to_bv 64 PC_P3). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2). unfold at_P3.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [exact HRZF|].
split. { unfold s_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)),
(GK 18%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split. { apply (post_mem_kept Lc Ac memc mem2 mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ([(ch_c C, CHT_SIZE); (ch_f C, 4 * T)] ++ newb T' p1 x1 h1 u1 f1) HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB ltac:(intros b Hb; apply in_app_iff; right; exact Hb) PM).
- intros a Ha Hs. apply KH2; [exact Ha | exact Hs].
- intros b m k Hb Hk. apply (KB2 b m k); [| exact Hk]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_app_iff; right; apply in_app_iff; right; exact Hb]. }
split. { unfold p_struct. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact PS | reflexivity |]. intros k Hk. apply (KB2 (ch_c C) CHT_SIZE k); [| exact Hk].
apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
exact HB2.
Qed.
End j.
Section t.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab).
Definition C2 : cht := mkCHT (ch_c C) f1 h1 u1 p1 x1 T' h1 u1 T' K (ents_below (ch_H C) (ch_T C)).
Hypothesis KINC : forall regs1 Lc Ac memc mdc, AT_INC regs1 Lc Ac memc mdc i ha pnew fimg imgl C2 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_INC) memc (seg_rom ubs2segs)) mdc) POST.
Definition ss_P3 : sstate := mkSS PC_P3 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 5168 0 0 [mkChunk 72 (CVal 8 (SOff 32%nat 0)); mkChunk 40 (CVal 8 (SOff 33%nat 0))] ;
YQ0b.mkRegion (Some 20%nat) 0 48 0 24 [] ] None
(mkFacts [(2%nat, mkAF CEIL_MIN (2^63) 4)] [] []).
Theorem P3_stretch : forall regs1 Lc Ac memc mdc, AT_P3 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_P3) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G24 & G25 & G18 & G26 & G20 & G9 & G8 & G21) & PM & PS & RZB).
pose proof PM as (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & S72 & Hfc & Hobj & Hcg & Himg & Hpn & Hfi & HCA & HTK & Hch' & HK & Hinv & HT & Hch & RhS & RuS & RTS & EhS & EuS & Hz).
pose proof Hslots as (M8 & M16 & M24 & M48).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). pose proof (ts_chain_ok _ Hch') as (RT1' & RT2' & RT3').
pose proof HK as ((M1 & M2 & M3 & M4 & M5) & (N1 & _) & _). rewrite HTK in M1, M2, M3, M4, M5, N1.
set (T := ch_T C) in *. unfold RGB_NMAX in HNmax.
assert (INB : forall b, In b (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE)] ++ newb T' p1 x1 h1 u1 f1) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]).
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (Q0 & Q1 & _). lia. }
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
destruct (RNG f1 (4 * T') ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rw0 Rw1].
destruct (RNG u1 T' ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rv0 Rv1].
destruct (RNG h1 (3 * T') ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rg0 Rg1].
assert (HfN : 0 < fmt * N) by (clear - Hfmt Hi; nia).
destruct (RNG img (fmt * N) ltac:(apply INB; apply in_app_iff; left; unfold BASE; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; unfold img_block, fmt_okb; destruct Hfmt as [-> | ->]; left; reflexivity) HfN) as [Ri0 Ri1].
assert (CSEP : forall y, In y (BASE0 ++ newb T' p1 x1 h1 u1 f1) -> ch_c C + 48 <= fst y \/ fst y + snd y <= ch_c C).
{ intros y Hy. pose proof (perm_sep API Lc Ac memc mdc (ch_c C, CHT_SIZE) y (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) (newb T' p1 x1 h1 u1 f1) HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X. apply X.
- rewrite <- !app_assoc. exact RZB.
- apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy|Hy]; [left; apply in_app_iff; left; exact Hy | right; exact Hy]. }
set (E := Ereg regs1 (map (Z_to_bv 64) [ha; fmt] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 ha) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 fmt) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HE24 : ew E 24 = Z_to_bv 64 h1) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE25 : ew E 25 = Z_to_bv 64 u1) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HE26 : ew E 26 = Z_to_bv 64 f1) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E ss_P3 (mkst regs1 (Z_to_bv 64 PC_P3) memc (seg_rom ubs2segs))).
{ unfold ss_P3. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
+ rewrite HU2. split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
assert (CK : forall off nn v, slot regs0 memc off v -> 0 <= v < 2 ^ 64 -> ew (Ereg regs1 (map (Z_to_bv 64) [ha; fmt] ++ [])) nn = Z_to_bv 64 v ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) [ha; fmt] ++ [])) memc SP (mkChunk off (CVal 8 (SOff nn 0)))).
{ intros off nn v Hs Hv Hn. eapply (chunk_ok_val _ _ _ _ _ _ _ v); [cbn [sv_denot]; rewrite Z.add_0_r, Hn, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact Hs. }
apply Forall_cons; [apply (CK 72 32%nat ha S72); [destruct Hha as [-> | [-> _]]; lia | exact HE32]|].
apply Forall_cons; [apply (CK 40 33%nat fmt S40); [lia | exact HE33]|]. apply Forall_nil.
+ rewrite HU20. split; [lia|]. split; [lia|]. split; [| constructor]. intros o Ho. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE o HHc ltac:(apply INB; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity) ltac:(unfold CHT_SIZE; lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU20. unfold sp, sp0 in *. repeat split; try exact I. clear - Rc1 Hceil HRv HFv. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16. unfold sp, sp0 in *. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_P3) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ PC_INC.
{ apply wr_ok_cons_ro; [cbn; lia|]. eapply wr_ok_cons_gen; [reflexivity | exact HU20 | cbn [r_wlo r_whi]; intros a Ha |]; [| apply wr_ok_nil].
apply (wr_byte_tmp API L A regs0 r g bef beffmt s N img fmt rest Lc Ac memc mdc ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE)] ++ newb T' p1 x1 h1 u1 f1) (ch_c C) CHT_SIZE a HHc); [| exact HB0 | apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | unfold CHT_SIZE; lia | unfold CHT_SIZE; lia].
rewrite <- ?app_assoc. exact RZB. }
cbn [ms_mem mkst] in HF.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (ch_c C <= a < ch_c C + 24) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hna. mb_frame_g HF; [reflexivity | lia | rewrite HU20; lia]. }
assert (V0 : val_mem ubs2segs (ms_mem ms) (ch_c C) 8 f1).
{ replace (ch_c C) with (ch_c C + 0) by lia. apply (st_chunk_val_g E _ _ 1%nat _ 20%nat 0 8%N (SOff 26 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU20 | cbn [sv_denot]; rewrite Z.add_0_r, HE26, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
assert (V8 : val_mem ubs2segs (ms_mem ms) (ch_c C + 8) 8 h1).
{ apply (st_chunk_val_g E _ _ 1%nat _ 20%nat 8 8%N (SOff 24 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU20 | cbn [sv_denot]; rewrite Z.add_0_r, HE24, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
assert (V16 : val_mem ubs2segs (ms_mem ms) (ch_c C + 16) 8 u1).
{ apply (st_chunk_val_g E _ _ 1%nat _ 20%nat 16 8%N (SOff 25 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU20 | cbn [sv_denot]; rewrite Z.add_0_r, HE25, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 81312) with (Z_to_bv 64 PC_INC).
apply (KINC (ms_regs ms) Lc Ac (ms_mem ms) mdc). unfold at_INC.
split. { apply (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc _ mdc HINV HJ). intros a Ha Hna. apply KEEP; lia. }
split. { unfold rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)). split; [exact G2 | split; [exact G3 | exact G4]]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|].
split. { unfold hist_regs, C2. cbn [ch_T ch_u ch_h ch_f ch_c].
split; [rewrite (GK 9%bv ltac:(cbv; auto 20)); exact G9|].
split; [jreg HS (18%bv:reg) as Hq; rewrite Hq, HE33; reflexivity|].
split; [jreg HS (19%bv:reg) as Hq; rewrite Hq, HE32; reflexivity|].
split; [rewrite (GK 20%bv ltac:(cbv; auto 20)); exact G20|].
split; [rewrite (GK 8%bv ltac:(cbv; auto 20)); exact G8|].
rewrite (GK 21%bv ltac:(cbv; auto 20)); exact G21. }
assert (KS : forall off v, 0 <= off -> off + 8 <= RGBA_FRAME -> slot regs0 memc off v -> slot regs0 (ms_mem ms) off v).
{ intros off v H0 H1 Hsl. unfold slot in *. apply (val_mem_kept8 memc); [exact Hsl|]. intros k Hk. apply KEEP; unfold sp, sp0 in *; lia. }
assert (KBL : forall b n a, In (b, n) (BASE0 ++ newb T' p1 x1 h1 u1 f1) -> b <= a < b + n -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros b n a Hb Ha. pose proof (CSEP (b, n) Hb) as X. cbn [fst snd] in X.
destruct (RNG b n ltac:(apply INB; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_app_iff; right; apply in_app_iff; right; exact Hb]) ltac:(lia)) as [Rb0 Rb1].
apply KEEP; lia. }
unfold hist_mem, C2. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
split. { unfold slots_mid, SL_N, SL_cfp, SL_new, SL_fimg in *. repeat split; (apply KS; [lia | lia | assumption]). }
split; [apply KS; unfold SL_32 in *; [lia | lia | exact S32]|].
split; [apply KS; unfold SL_40 in *; [lia | lia | exact S40]|].
split; [apply KS; unfold SL_56 in *; [lia | lia | exact S56]|].
split; [apply KS; unfold SL_64 in *; [lia | lia | exact S64]|].
split; [apply KS; unfold SL_80 in *; [lia | lia | exact S80]|].
split; [apply KS; unfold SL_112 in *; [lia | lia | exact S112]|].
split; [apply KS; unfold SL_120 in *; [lia | lia | exact S120]|].
split. { unfold fcfg_at in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 29); [exact Hfc | reflexivity |]. intros k Hk. unfold OFF_fcfg. apply KEEP; unfold sp, sp0 in *; lia. }
split. { unfold rgb_obj in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros k Hk. apply (KBL r RGB_SIZE); [apply in_app_iff; left; left; reflexivity | lia]. }
split. { eapply (cgif_at_kept _ _ g s N (cgif_blocks g s N) []); [rewrite app_nil_r; apply Permutation_refl | exact Hcg |].
intros b n k Hbn Hk. apply (KBL b n); [apply in_app_iff; left; right; apply in_app_iff; left; exact Hbn | lia]. }
split. { destruct Himg as [Ha Hl]. split; [|exact Hl]. eapply arr8_frame; [exact Ha|]. intros a Ha'. apply (KBL img (fmt * N)); [| rewrite <- Hl; exact Ha'].
apply in_app_iff. left. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. unfold img_block, fmt_okb. destruct Hfmt as [-> | ->]; left; reflexivity. }
split. { unfold cht_ok. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
split. { apply (obj_at_cht_set_fhu memc (ms_mem ms) (ch_c C) (ch_f C) (ch_hS C) (ch_uS C) p1 x1 (ht_cnt K) T' f1 h1 u1 PS); [| exact V0 | exact V8 | exact V16 | lia | lia | lia]. intros a Ha Hna. apply KEEP; lia. }
split. { destruct HCA as (Af & Ah & Au & Ap & Ax). unfold cht_arrays. split; [|split; [|split; [|split]]].
- eapply arr32_frame; [exact Af|]. intros a Ha. apply (KBL f1 (4 * T')); [apply in_app_iff; right; cbn; auto 10 | rewrite <- M3; lia].
- eapply arr8_frame; [exact Ah|]. intros a Ha. apply (KBL h1 (3 * T')); [apply in_app_iff; right; cbn; auto 10 | rewrite <- M2; lia].
- eapply arr8_frame; [exact Au|]. intros a Ha. apply (KBL u1 T'); [apply in_app_iff; right; cbn; auto 10 | rewrite <- M1; lia].
- eapply arr8_frame; [exact Ap|]. intros a Ha. apply (KBL p1 (3 * T')); [apply in_app_iff; right; cbn; auto 10 | rewrite <- M5; lia].
- eapply arr32_frame; [exact Ax|]. intros a Ha. apply (KBL x1 (4 * T')); [apply in_app_iff; right; cbn; auto 10 | rewrite <- M4; lia]. }
split; [exact HK|]. split; [exact HTK|]. split; [exact Hch'|]. split; [lia|]. split; [lia | lia]. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split. { rewrite <- (perm_zsum (ch_ent C) (ents_below (ch_H C) (ch_T C))); [exact Hz|]. replace (ch_T C) with (ht_T (ch_H C)) by exact HT. exact (rehash_done (ch_H C) (ch_ent C) Hinv). }
split; [exact Hpn|]. split; [exact Hfi|].
eapply Permutation_trans; [exact RZB|]. unfold cht_blks, cht_blocks, newb. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T]. perm_tac.
Qed.
End t.
End e.
End d.
