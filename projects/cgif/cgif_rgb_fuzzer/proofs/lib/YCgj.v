(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdv YCgl YCg2 YCgi YCg4 YCg0 YCfy YCg8 YCg1.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition A_rd : Z := 0x8bc2c.
Definition rd_written (cx : lzw_acx) (lp : Z) (a : Z) : Prop :=
(z_sp cx - 336 - 4096 <= a < z_sp cx - 304) \/ (z_ctx cx + 60 <= a < z_ctx cx + 68) \/ (z_ld cx + 2 * lp <= a < z_ld cx + 2 * lp + 2) \/
(z_ti cx <= a < z_ti cx + z_tisz cx) \/ (z_lm cx <= a < z_lm cx + 8192) \/ (z_lc cx <= a < z_lc cx + 4096) \/ (z_li cx <= a < z_li cx + 8192).
Definition rd_untouched (cx : lzw_acx) (lp : Z) (a : Z) : Prop := ~ rd_written cx lp a.
Definition in_rng (lo hi a : Z) : Prop := lo <= a < hi.
Definition acommon_facts0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, APTR 4); (23%nat, mkAF SB SB 0); (22%nat, mkAF 2 2 0); (25%nat, mkAF 2 256 0);
(32%nat, APTR 4); (33%nat, APTR 4); (34%nat, APTR 4); (35%nat, APTR 4); (36%nat, APTR 4); (37%nat, APTR 4);
(38%nat, APTR 0); (39%nat, mkAF 1 100000000 0); (40%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 4097) 0);
(41%nat, mkAF 0 (2^27 - 2) 0);
(44%nat, mkAF 0 (2^47 - 16) 3); (45%nat, mkAF 4 512 0); (46%nat, mkAF 0 12 0) ].
Definition rctx_chunks (k60 : bool) : list YQ0b.chunk :=
[YQ0b.mkChunk 0 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 32 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 40 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 48 (CVal 8 (SOff 38 0)); YQ0b.mkChunk 56 (CVal 4 (SOff 39 0))] ++
(if k60 then [YQ0b.mkChunk 60 (CVal 4 (SOff 41 0))] else []).
Definition rctx_region (k60 : bool) : YQ0b.region := YQ0b.mkRegion (Some 8%nat) 0 72 60 68 (rctx_chunks k60).
Definition agen_ptrs (m : word -> option byte) (cx : lzw_acx) : Prop :=
let g := z_ctx cx in
val_mem trbsegs m g 8 (z_ti cx) /\ val_mem trbsegs m (g + 8) 8 (z_lm cx) /\
val_mem trbsegs m (g + 16) 8 (z_lc cx) /\ val_mem trbsegs m (g + 24) 8 (z_li cx) /\
val_mem trbsegs m (g + 32) 8 (z_tm cx) /\ val_mem trbsegs m (g + 40) 8 (z_ld cx) /\
val_mem trbsegs m (g + 48) 8 (z_img cx) /\ val_mem trbsegs m (g + 56) 4 (z_nP cx).
Lemma agen_ptrs_of_at : forall m cx lp dp mp, agen_at m cx lp dp mp -> agen_ptrs m cx.
Proof. intros m cx lp dp mp (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _). unfold agen_ptrs. repeat split; assumption. Qed.
Lemma agen_at_of_ptrs : forall m m' cx lp' dp' mp',
agen_ptrs m cx ->
(forall a, z_ctx cx <= a < z_ctx cx + 60 -> mbyte trbsegs m' a = mbyte trbsegs m a) ->
val_mem trbsegs m' (z_ctx cx + 60) 4 lp' -> val_mem trbsegs m' (z_ctx cx + 64) 2 dp' -> val_mem trbsegs m' (z_ctx cx + 66) 2 mp' ->
agen_at m' cx lp' dp' mp'.
Proof.
intros m m' cx lp' dp' mp' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hfr Vlp Vdp Vmp.
unfold agen_at. repeat split; try assumption;
intros k Hk; (rewrite Hfr; [| cbn in Hk; lia]); first [apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8]; exact Hk.
Qed.
Definition rd_ss (pc : Z) (sr : list sv) (rs : smem) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr rs None (mkFacts (acommon_facts0 ++ fs) cs (acommon_alias ++ al)).
Definition rd_regs : list sv := sr_set (sr_set asr_fix 10%bv (SOff 8 0)) 11%bv (SOff 25 0).
Definition ss_rd0 : sstate :=
rd_ss A_rd rd_regs [rctx_region true; stack_region 32; got_region; bcell_region 23; regw 60 2]
[ (60%nat, APTR 1) ] [ mkAC BC_GEU (SOff 60 0) (SOff 37 0) ] [ (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SLL (SOff 41 0) (SLit 1)), SOff 60 0) ].
Lemma U_tisz2 : forall E n idl, ew E n = Z_to_bv 64 idl -> 2 <= idl <= 256 ->
U E (SAlu ALU_SLL (SMd M_MUL (SOff n 0) (SOff n 0)) (SLit 1)) = 2 * idl * idl.
Proof.
intros E n idl Hn Hi.
assert (Hsq : idl * idl <= 256 * 256) by nia. assert (Hsq0 : 0 <= idl * idl) by nia.
rewrite (U_sll1_small E _ (idl * idl)); [lia | | lia | lia].
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n idl Hn) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma arr16_zeros_aview : forall H (mem : word -> option byte) base n,
(forall a, base <= a < base + 2 * Z.of_nat n -> mbyte trbsegs (mrestrict H mem) a = Some (Z_to_bv 8 0)) ->
arr16 trbsegs (mrestrict H mem) base (repeat 0 n).
Proof. intros H mem base n Hz. apply arr16_zeros. exact Hz. Qed.
Lemma mbyte_zero_of_aview : forall H (m : word -> option byte) a,
aview trbsegs H m a = Some 0 -> mbyte trbsegs (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
intros H m a Hz. destruct (aview_byte trbsegs H m a 0 Hz) as (b & Hb & Hv & _). rewrite Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_0_l by (vm_compute; discriminate). lia.
Qed.
Lemma acommon_facts0_ok : forall E cx lp dp mp,
ew E 2 = Z_to_bv 64 (z_sp cx - 304) -> ew E 8 = Z_to_bv 64 (z_ctx cx) -> ew E 23 = Z_to_bv 64 SB -> ew E 22 = Z_to_bv 64 2 -> ew E 25 = Z_to_bv 64 (z_idl cx) ->
ew E 32 = Z_to_bv 64 (z_ti cx) -> ew E 33 = Z_to_bv 64 (z_lm cx) -> ew E 34 = Z_to_bv 64 (z_lc cx) -> ew E 35 = Z_to_bv 64 (z_li cx) ->
ew E 36 = Z_to_bv 64 (z_tm cx) -> ew E 37 = Z_to_bv 64 (z_ld cx) -> ew E 38 = Z_to_bv 64 (z_img cx) -> ew E 39 = Z_to_bv 64 (z_nP cx) ->
ew E 40 = Z_to_bv 64 (z_nimg cx) -> ew E 41 = Z_to_bv 64 lp -> ew E 42 = Z_to_bv 64 dp -> ew E 43 = Z_to_bv 64 mp ->
ew E 44 = Z_to_bv 64 (z_pR cx) -> ew E 45 = Z_to_bv 64 (2 * z_idl cx) -> ew E 46 = Z_to_bv 64 (z_icl cx) ->
acx_ok cx -> acx_ranges cx -> 0 <= lp <= 2 ^ 27 - 2 ->
atoms_ok E acommon_facts0.
Proof.
intros E cx lp dp mp HE2 HE8 HE21 HE22 HE25 HE32 HE33 HE34 HE35 HE36 HE37 HE38 HE39 HE40 HE41 HE42 HE43 HE44 HE45 HE46 Hcx Hrg Hlp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof Hrg as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3).
cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
assert (Hsp16 : (z_sp cx - 304) mod 16 = 0).
{ pose proof (Z.div_mod (z_sp cx) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (z_sp cx / 16) - 304) with ((z_sp cx / 16 - 19) * 16) by lia. apply Z_mod_mult. }
clear Hcx Hrg HMR HMR0 EMR.
cbn [atoms_ok acommon_facts0]. unfold afact_ok, APTR, z_nimg in *. cbn [af_lo af_hi af_al2].
rewrite ?C1, ?C2, ?C3, ?C4, ?C5, ?HTS, ?Has in *. clear C2 C3 C4 C5 HTS Has.
rewrite HE2, HE8, HE21, HE22, HE25, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE40, HE41, HE44, HE45, HE46.
clear E HE2 HE8 HE21 HE22 HE25 HE32 HE33 HE34 HE35 HE36 HE37 HE38 HE39 HE40 HE41 HE42 HE43 HE44 HE45 HE46.
ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *.
repeat match goal with |- _ /\ _ => split end.
all: rewrite ?unsigned_lit_small by lia.
all: change (2 ^ 4) with 16 || idtac; change (2 ^ 3) with 8 || idtac; change (2 ^ 0) with 1 || idtac; rewrite ?Z.mod_1_r.
all: first [assumption | lia | match goal with |- ?g => idtac "SEEDFACT" g end].
Qed.
Lemma rctx_region_ok : forall cx regs regs0 lp dp mp more (m : word -> option byte) k60,
acx_ok cx -> acx_ranges cx -> alzw_regs_core regs cx -> agen_ptrs m cx ->
(k60 = true -> val_mem trbsegs m (z_ctx cx + 60) 4 lp) ->
(forall a, z_ctx cx + 60 <= a < z_ctx cx + 68 -> writable_at trbsegs m a) ->
0 <= lp <= 2 ^ 27 - 2 ->
region_ok trbsegs (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) m (rctx_region k60).
Proof.
intros cx regs regs0 lp dp mp more m k60 Hcx Hrg HF HG V60 Hwg Hlp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof Hrg as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3).
cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
rewrite ?C1, ?C2, ?C3, ?C4, ?C5 in *. clear C2 C3 C4 C5.
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56).
pose proof (AE_ctx regs cx lp dp mp regs0 more HF) as HE8.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE32. pose proof (AE_lm regs cx lp dp mp regs0 more) as HE33.
pose proof (AE_lc regs cx lp dp mp regs0 more) as HE34. pose proof (AE_li regs cx lp dp mp regs0 more) as HE35.
pose proof (AE_tm regs cx lp dp mp regs0 more) as HE36. pose proof (AE_ld regs cx lp dp mp regs0 more) as HE37.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE38. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE39.
pose proof (AE_lp regs cx lp dp mp regs0 more) as HE41.
clear HF Hcx Hrg HMR HMR0 Hgp Htp EMR.
unfold region_ok, rctx_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply Hwg. lia. }
unfold rctx_chunks.
Ltac ack0 S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl || lia | first [exact S | rewrite Z.add_0_r; exact S] ].
apply Forall_app. split.
- constructor; [ack0 V0 HE32|]. constructor; [ack0 V8 HE33|]. constructor; [ack0 V16 HE34|]. constructor; [ack0 V24 HE35|].
constructor; [ack0 V32 HE36|]. constructor; [ack0 V40 HE37|]. constructor; [ack0 V48 HE38|]. constructor; [ack0 V56 HE39|]. constructor.
- destruct k60; [|constructor]. constructor; [ack0 (V60 eq_refl) HE41 | constructor].
Qed.
Lemma rd_st_ok0 : forall cx regs regs0 lp dp mp more (m : word -> option byte) pc sr rs fs cs al,
acx_ok cx -> acx_ranges cx -> alzw_regs_core regs cx -> 0 <= lp <= 2 ^ 27 - 2 ->
let E := Ereg regs (acx_extra cx lp dp mp regs0 ++ more) in
regs_ok E sr regs ->
regions_wf rs = true ->
Forall (region_ok trbsegs E m) rs -> pairwise_disjoint E rs ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok trbsegs E (rd_ss pc sr rs fs cs al) (mkst regs (Z_to_bv 64 pc) m (seg_rom trbsegs)).
Proof.
intros cx regs regs0 lp dp mp more m pc sr rs fs cs al Hcx Hrg HF Hlp E Hsr Hwf Hrs Hpd Hfs Hcs Hal.
subst E. pose proof asan_consts as (C1 & _).
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof Hrg as (HR & [Hb4 Hbz] & Hbi1 & Hbi2 & Hbi3).
pose proof (AE_sp regs cx lp dp mp regs0 more HF) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HF) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HF) as HE21. pose proof (AE_two regs cx lp dp mp regs0 more HF) as HE22.
pose proof (AE_idl regs cx lp dp mp regs0 more HF) as HE25.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE32. pose proof (AE_lm regs cx lp dp mp regs0 more) as HE33.
pose proof (AE_lc regs cx lp dp mp regs0 more) as HE34. pose proof (AE_li regs cx lp dp mp regs0 more) as HE35.
pose proof (AE_tm regs cx lp dp mp regs0 more) as HE36. pose proof (AE_ld regs cx lp dp mp regs0 more) as HE37.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE38. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE39.
pose proof (AE_nimg regs cx lp dp mp regs0 more) as HE40. pose proof (AE_lp regs cx lp dp mp regs0 more) as HE41.
pose proof (AE_dp regs cx lp dp mp regs0 more) as HE42. pose proof (AE_mp regs cx lp dp mp regs0 more) as HE43.
pose proof (AE_pR regs cx lp dp mp regs0 more) as HE44. pose proof (AE_idl2 regs cx lp dp mp regs0 more) as HE45.
pose proof (AE_icl regs cx lp dp mp regs0 more) as HE46.
apply entry_st_ok_full.
- exact Hsr.
- exact Hwf.
- exact Hrs.
- exact Hpd.
- split; [|split; [exact Hcs |]].
+ unfold rd_ss. cbn [f_atoms]. apply atoms_ok_app; [|exact Hfs].
eapply (acommon_facts0_ok _ cx lp dp mp); eassumption.
+ unfold rd_ss. cbn [f_alias]. split; [|exact Hal].
apply (alias_nimg _ 38 40 (z_img cx) HE38 HE40). clear - C1 Hb4 Hbi1 Hbi2 Hbi3 HnP. lia.
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Local Ltac sep HSEP i j := septac HSEP i j; lia.
Lemma tard_run : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT lp TM raw,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal trbsegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
z_gp cx = as_gp B -> z_tp cx = as_tp B ->
alzw_regs_fix regs cx -> agen_ptrs (mrestrict (w_H W7) memT) cx -> val_mem trbsegs (mrestrict (w_H W7) memT) (z_ctx cx + 60) 4 lp ->
arr16 trbsegs (mrestrict (w_H W7) memT) (z_tm cx) TM -> length TM = Z.to_nat (2049 * z_idl cx) ->
getr regs 10 = w64 (z_ctx cx) -> getr regs 11 = w64 (z_idl cx) -> getr regs 1 = raw -> YK0s.ret_ok raw ->
0 <= lp -> lp < z_cap cx -> lp <= 134217726 ->
SRr trbsegs W7 (mkCfg (mkst regs (Z_to_bv 64 A_rd) memT (seg_rom trbsegs)) mdT)
(fun W' c' => W' = W7 /\ exists regs' mem' md',
c' = mkCfg (mkst regs' raw mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
alzw_regs_fix regs' cx /\ aregs_preserved regs regs' /\ getr regs' 24 = getr regs 24 /\
agen_at (mrestrict (w_H W7) mem') cx (lp + 1) (z_idl cx + 2) 1 /\
arr16 trbsegs (mrestrict (w_H W7) mem') (z_tm cx) TM /\
(forall a, 0 <= a < 2 ^ 64 -> in_rng (z_ti cx) (z_ti cx + z_tisz cx) a -> mbyte trbsegs (mrestrict (w_H W7) mem') a = Some (Z_to_bv 8 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> in_rng (z_lm cx) (z_lm cx + 8192) a -> mbyte trbsegs (mrestrict (w_H W7) mem') a = Some (Z_to_bv 8 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> in_rng (z_lc cx) (z_lc cx + 4096) a -> mbyte trbsegs (mrestrict (w_H W7) mem') a = Some (Z_to_bv 8 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> in_rng (z_li cx) (z_li cx + 8192) a -> mbyte trbsegs (mrestrict (w_H W7) mem') a = Some (Z_to_bv 8 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_written cx lp a -> mbyte trbsegs (mrestrict (w_H W7) mem') a = mbyte trbsegs (mrestrict (w_H W7) memT) a)).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT lp TM raw HCX HRG HSEP (HBg & HBi & HBt) HTOK HJ Hzgp Hztp HFX HG V60 ATM LenTM
H10 H11 Hra Hraw Hlp0 Hlpc Hlpm.
set (dp := 0). set (mp := 0).
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HJ as (HAR & _). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
assert (HBti : In (z_ti cx, 2 * z_idl cx * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; right; left; reflexivity).
assert (HBlm : In (z_lm cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity).
assert (HBlc : In (z_lc cx, 4096) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity).
assert (HBli : In (z_li cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity).
assert (HBtm : In (z_tm cx, 4098 * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ltac:(pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)); unfold lzw_MR; lia)) as Hrqld.
pose proof (req_size_pos 8192 ltac:(lia)) as Hrq8. pose proof (req_size_pos 4096 ltac:(lia)) as Hrq4. pose proof (req_size_pos (2 * z_idl cx * z_idl cx) ltac:(lia)) as Hrqti.
assert (Actx : forall blc lyq i, In (z_ctx cx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ctx cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ctx cx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]. }
assert (Ald : forall blc lyq i, In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) blc -> 0 <= i < req_size (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ->
awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ld cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ld cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; left; reflexivity)); [exact Hb | exact Hi]. }
assert (Ati : forall blc lyq i, In (z_ti cx, 2 * z_idl cx * z_idl cx) blc -> 0 <= i < req_size (2 * z_idl cx * z_idl cx) ->
awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ti cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ti cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; right; left; reflexivity)); [exact Hb | exact Hi]. }
assert (Alm : forall blc lyq i, In (z_lm cx, 8192) blc -> 0 <= i < req_size 8192 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_lm cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_lm cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity)); [exact Hb | exact Hi]. }
assert (Alc : forall blc lyq i, In (z_lc cx, 4096) blc -> 0 <= i < req_size 4096 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_lc cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_lc cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity)); [exact Hb | exact Hi]. }
assert (Ali : forall blc lyq i, In (z_li cx, 8192) blc -> 0 <= i < req_size 8192 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_li cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_li cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity)); [exact Hb | exact Hi]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ld cx) _ HAR HBld) as (_ & _ & Hldceil & _ & Hldpres & _).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Htisz : 8 <= 2 * z_idl cx * z_idl cx <= 131072) by (clear - Hidl; split; [nia|nia]).
unfold z_cap, cap in Hlpc. unfold z_tisz, z_tmsz in *.
assert (Hsws : forall a, z_sp cx - 336 <= a < z_sp cx -> apresent (w_H W7) memT a).
{ intros a Ha. apply (proj1 (awr_byte_present trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ ltac:(left; lia))). }
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
set (m := mrestrict (w_H W7) memT) in *.
remember [Z_to_bv 64 (z_ld cx + 2 * lp)] as more eqn:Hmore.
remember (Ereg regs (acx_extra cx lp dp mp regs ++ more)) as E eqn:HE0.
assert (HE60 : ew E 60 = Z_to_bv 64 (z_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0), Hmore; reflexivity).
pose proof (AE_sp regs cx lp dp mp regs more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs more HFC) as HE21. pose proof (AE_idl regs cx lp dp mp regs more HFC) as HE25.
pose proof (AE_gp regs cx lp dp mp regs more HFC) as HE3. pose proof (AE_tp regs cx lp dp mp regs more HFC) as HE4.
pose proof (AE_ti regs cx lp dp mp regs more) as HE32. pose proof (AE_lm regs cx lp dp mp regs more) as HE33.
pose proof (AE_lc regs cx lp dp mp regs more) as HE34. pose proof (AE_li regs cx lp dp mp regs more) as HE35.
pose proof (AE_tm regs cx lp dp mp regs more) as HE36. pose proof (AE_ld regs cx lp dp mp regs more) as HE37.
pose proof (AE_lp regs cx lp dp mp regs more) as HE41. pose proof (AE_dp regs cx lp dp mp regs more) as HE42. pose proof (AE_mp regs cx lp dp mp regs more) as HE43.
rewrite <- HE0 in HE2, HE8, HE21, HE25, HE3, HE4, HE32, HE33, HE34, HE35, HE36, HE37, HE41, HE42, HE43.
assert (HE1 : ew E 1 = raw) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 1%bv 1) by reflexivity; exact Hra).
assert (HS1 : st_ok trbsegs E ss_rd0 (mkst regs (Z_to_bv 64 A_rd) m (seg_rom trbsegs))).
{ unfold ss_rd0. rewrite HE0. apply (rd_st_ok0 cx regs regs lp dp mp more m A_rd); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - lia.
- rewrite HE0. unfold rd_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply (regs_ok_fix regs cx lp dp mp regs more HFX); lia | intros X0; discriminate X0 |] | intros X0; discriminate X0 |];
rewrite <- HE0; cbn [sv_denot].
+ rewrite HE8, Z.add_0_r, unsigned_lit_small by lia. exact H10.
+ rewrite HE25, Z.add_0_r, unsigned_lit_small by lia. exact H11.
- vm_compute; reflexivity.
-
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
+ rewrite HE0. apply (rctx_region_ok cx regs regs lp dp mp more m true HCX HRG HFC HG ltac:(intros _; exact V60)); [|lia].
intros a Ha. apply (apresent_writable trbsegs). apply (proj1 (Hcpres a ltac:(lia))).
+ unfold region_ok, stack_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hsws. lia.
+ unfold region_ok, got_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs E _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W7) memT _ _ Kgot).
+ unfold region_ok, bcell_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs E _ 0 701048 8 (SOff 23 0) SB);
[cbn [sv_denot]; rewrite HE21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W7) memT _ _ Kcell).
+ apply (region_ok_regw _ E m 60 2 (z_ld cx + 2 * lp) HE60); [lia | lia | lia |].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hldpres (z_ld cx + 2 * lp + o) ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, stack_region, got_region, bcell_region, regw, rctx_region, A_GOT_shadow, A_shadow_glob;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val app].
rewrite HE8, HE2, HE60, !unsigned_lit_small by lia.
pose proof (proj1 Rg1) as Rg0. unfold zone2, off_img, in_app in Rg1. unfold zone2, off_img, in_app in Rld1. septac HSEP 0%nat 6%nat.
repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE60, !unsigned_lit_small by lia. change (2 ^ 1) with 2.
repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- cbn [conds_ok]. split; [apply (cond_geu E 60 0 37 0 (z_ld cx + 2 * lp) (z_ld cx) HE60 HE37); lia | exact I].
- cbn [alias_ok]. split; [| exact I]. apply (alias_b2i' E 37 41 60 (z_ld cx) lp HE37 HE41 HE60); lia. }
idtac "SEED OK".
cbn [ss_rd0 rd_ss] in HS1. subst m. rewrite <- restrict_mkst_fx in HS1. rename HS1 into HS.
set (m := mrestrict (w_H W7) memT) in *.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> rd_untouched cx lp a -> mbyte trbsegs (mrestrict (w_H W7) memT) a = mbyte trbsegs (mrestrict (w_H W7) memT) a) by (intros; reflexivity).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
shok_auto SHOK (SOff 23 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 A_rd) memT (seg_rom trbsegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 A_rd) memT (seg_rom trbsegs))) in HJ.
Local Ltac zsep HSEP C :=
lazymatch C with
| in_rng (z_ti _) _ => unfold in_rng in *; septac HSEP 1%nat 6%nat; septac HSEP 0%nat 1%nat; septac HSEP 1%nat 2%nat; septac HSEP 1%nat 3%nat; septac HSEP 1%nat 4%nat; lia
| in_rng (z_lm _) _ => unfold in_rng in *; septac HSEP 2%nat 6%nat; septac HSEP 0%nat 2%nat; septac HSEP 1%nat 2%nat; septac HSEP 2%nat 3%nat; septac HSEP 2%nat 4%nat; lia
| in_rng (z_lc _) _ => unfold in_rng in *; septac HSEP 3%nat 6%nat; septac HSEP 0%nat 3%nat; septac HSEP 1%nat 3%nat; septac HSEP 2%nat 3%nat; septac HSEP 3%nat 4%nat; lia
| in_rng (z_li _) _ => unfold in_rng in *; septac HSEP 4%nat 6%nat; septac HSEP 0%nat 4%nat; septac HSEP 1%nat 4%nat; septac HSEP 2%nat 4%nat; septac HSEP 3%nat 4%nat; lia
| _ => unfold rd_untouched, rd_written, z_tisz in *; lia
end.
Local Ltac fold_step T HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9 :=
lazymatch type of T with forall a, _ -> _ -> mbyte _ ?mn a = mbyte _ ?mo a =>
repeat match goal with
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte trbsegs mo a = mbyte trbsegs ?mz a |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte trbsegs mn a = mbyte trbsegs mz a)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte trbsegs mo a = Some ?v |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte trbsegs mn a = Some v)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
end
end; clear T.
Local Ltac awr5 cx lp AG HE8 HE2 HE60 Actx HBg Ald HBld :=
cbn [ss_mem ss_rd0 rd_ss];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (z_ctx cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi rctx_region]; intros a Ha; replace a with (z_ctx cx + (a - z_ctx cx)) by lia; apply Actx; [exact HBg | lia]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-304));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 2%nat) by lia; rewrite HE2, unsigned_lit_small by lia; lia
| cbn; lia | cbn; lia
| apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 60%nat (z_ld cx + 2 * lp));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE60; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi regw]; intros a Ha; replace a with (z_ld cx + (a - z_ld cx)) by lia; apply Ald; [exact HBld | lia]
| apply awr_ok_nil ] ] ].
Local Ltac awr2 cx lp AG HE8 HE2 HE60 Actx HBg Ald HBld :=
cbn [ss_mem ss_rd0 rd_ss];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (z_ctx cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi rctx_region]; intros a Ha; replace a with (z_ctx cx + (a - z_ctx cx)) by lia; apply Actx; [exact HBg | lia]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-304));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 2%nat) by lia; rewrite HE2, unsigned_lit_small by lia; lia
| cbn; lia | cbn; lia
| apply awr_ok_nil ] ].
Local Ltac tstep cx lp ws AG HE8 HE2 HE60 HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9 :=
let T := fresh "T" in
lazymatch goal with HFr : frame_of ?Ef _ (mrestrict ?Hh ?ma) (mrestrict _ ?mb) |- _ =>
cbn [ss_mem ss_rd0 rd_ss] in HFr;
assert (T : forall a, 0 <= a < 2 ^ 64 ->
(~ (z_ctx cx + 60 <= a < z_ctx cx + 68) /\ ~ (z_sp cx - 336 <= a < z_sp cx - 304) /\ ~ (z_ld cx + 2 * lp <= a < z_ld cx + 2 * lp + 2)) ->
mbyte trbsegs (mrestrict Hh mb) a = mbyte trbsegs (mrestrict Hh ma) a)
by (intros a Ha (Hu1 & Hu2 & Hu3);
eapply (aframe_mbyte_list Ef _ _ _ ws a HFr Ha);
[ repeat (apply Forall2_cons;
[ first [ left; cbn; lia
| right; cbn [fst snd YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi rctx_region stack_region got_region bcell_region regw base_val ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; try rewrite (AG 2%nat) by lia;
rewrite ?HE8, ?HE2, ?HE60, ?unsigned_lit_small by lia; lia ] |]);
apply Forall2_nil
| cbn; repeat split; first [assumption | lia | exact I] ]);
clear HFr; try match goal with H : frame_of _ _ _ _ |- _ => clear H end; try match goal with H : mem_grows _ _ |- _ => clear H end;
fold_step T HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9
end.
Local Ltac oblkA AG HJ HB HEn HE21 v :=
let L := getLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff ?n ?c)) ?len =>
first [ rewrite (U_atom_off Ex n v c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n v); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HEn | lia] ];
eapply (obl_of_block trbsegs _ L _ _ _ _ _ Ex (SOff 23 0) _ len _ _ (proj1 HJ) HB);
[ rewrite (U_atom Ex 23 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?AG by lia; exact HE21 | unfold SB; lia]
| lia
| try change (req_size 72) with 72; first [ lia | match goal with |- _ <= _ + req_size ?nn => pose proof (req_size_pos nn ltac:(lia)); lia end ] ]
end.
Local Ltac obls cx lp AG HJ HBg HE8 HBld HE60 HE21 := try (oblkA AG HJ HBg HE8 HE21 (z_ctx cx)); try (oblkA AG HJ HBld HE60 HE21 (z_ld cx + 2 * lp)).
Local Ltac stretch cx lp HS HJ SHOK AG HE8 HE2 HE60 HE21 HBg HBld ws awr HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9 :=
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan; obls cx lp AG HJ HBg HE8 HBld HE60 HE21; [ awr | ];
[ tstep cx lp ws AG HE8 HE2 HE60 HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9 ].
Local Ltac mcall cx HS HJ AG HEd HE25 HE2 HE3 HE4 Hzgp Hztp dval nval raval HB Atmp :=
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
rreg HS (10%bv : bv 5) Ra0; rreg HS (11%bv : bv 5) Ra1; rreg HS (12%bv : bv 5) Ra2; rreg HS (1%bv : bv 5) Rra;
rreg HS (2%bv : bv 5) Rsp; rreg HS (3%bv : bv 5) Rgp; rreg HS (4%bv : bv 5) Rtp;
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset);
let L := getLAWS in let HSGL := aj_segs_low in
eapply SRr_bind;
[ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B L HSGL OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) _ _ _ _ _ _ _ _ _ _ _ _ 7
dval 0 nval (-336) (Z_to_bv 64 raval) HJ) end;
[ rewrite Ra0; eatom AG HEd
| rewrite Ra1; reflexivity
| first [ rewrite Ra2; reflexivity
| rewrite (st_ok_restrict_reg trbsegs _ _ _ _ (12%bv : bv 5) HS);
match goal with |- sv_denot ?Ex (sr_get ?sr ?r) = _ => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
rewrite denot_lit_U; unfold w64; f_equal; apply (U_tisz2 _ 25 (z_idl cx)); [eatom AG HE25 | lia] ]
| lia | lia | lia
| unfold spZ; rewrite Rsp; try rewrite (AG 2%nat) by lia; cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 2%nat) by lia;
rewrite HE2, (unsigned_lit_small (z_sp cx - 304)) by lia; rewrite unsigned_lit_small by lia; lia
| reflexivity | lia | unfold ESTACK; lia
| rewrite Rgp; try rewrite (AG 3%nat) by lia; rewrite HE3, Hzgp; reflexivity
| rewrite Rtp; try rewrite (AG 4%nat) by lia; rewrite HE4, Hztp; reflexivity
| exact Rra | vm_compute; reflexivity
| intros a Ha; split; [replace a with (dval + (a - dval)) by lia; apply Atmp; [exact HB | lia] | unfold ESTACK; lia]
| eapply (amem_range_of_block trbsegs B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| eapply (range_addressable_of_block trbsegs B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| intros _; eapply (shadow_hull_vis_of_block trbsegs B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| exact I ]
| cbv beta; clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp ].
Local Ltac mpost cx Heff Hfr dval nval Zname HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9 :=
let T := fresh "T" in
lazymatch type of Hfr with forall a, _ -> _ -> _ -> aview _ (w_H ?Wx) ?m2 a = aview _ _ ?m1 a =>
assert (Zname : forall a, 0 <= a < 2 ^ 64 -> in_rng dval (dval + nval) a -> mbyte trbsegs (mrestrict (w_H Wx) m2) a = Some (Z_to_bv 8 0))
by (intros a Ha Hd; unfold in_rng in Hd; replace a with (dval + (a - dval)) by lia; apply mbyte_zero_of_aview; rewrite (Heff (a - dval)) by lia; reflexivity);
assert (T : forall a, 0 <= a < 2 ^ 64 -> (~ (dval <= a < dval + nval) /\ ~ (z_sp cx - 336 - 4096 <= a < z_sp cx - 336)) ->
mbyte trbsegs (mrestrict (w_H Wx) m2) a = mbyte trbsegs (mrestrict (w_H Wx) m1) a)
by (intros a Ha [Hn1 Hn2]; apply (mbyte_of_aview trbsegs); apply Hfr; [exact Ha | exact Hn1 | unfold ESTACK; replace (z_sp cx + -336) with (z_sp cx - 336) by lia; exact Hn2]);
clear Heff Hfr; fold_step T HSEP R1 R2 R3 R4 R5 R6 R7 R8 R9
end.
Local Ltac keptR AG HE8 HE2 Hfr Hpres HSEP i :=
eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
lazymatch goal with
| |- bv_unsigned (ew _ 8) = _ => try rewrite (AG 8%nat) by lia; rewrite HE8
| |- bv_unsigned (ew _ 2) = _ => try rewrite (AG 2%nat) by lia; rewrite HE2
end; rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr;
[ lia
| revert Ha;
lazymatch goal with
| |- z_ctx _ + _ <= _ < _ -> _ => sep HSEP i 6%nat
| _ => lia
end
| unfold ESTACK; lia ]
| exact Hpres ].
stretch cx lp HS HJ SHOK AG HE8 HE2 HE60 HE21 HBg HBld
[(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 336, z_sp cx - 304); (0, 0); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2)]
ltac:(awr5 cx lp AG HE8 HE2 HE60 Actx HBg Ald HBld) HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
idtac "RUN1 OK".
mcall cx HS HJ AG HE32 HE25 HE2 HE3 HE4 Hzgp Hztp (z_ti cx) (2 * z_idl cx * z_idl cx) 0x8bd2c HBti Ati.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff1 & Hfr1 & Hpres2).
reseat HS HJ2 HP2 [0; 1]%nat AG ltac:(keptR AG HE8 HE2 Hfr1 Hpres2 HSEP 1%nat).
mpost cx Heff1 Hfr1 (z_ti cx) (2 * z_idl cx * z_idl cx) ZTI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 0x8bd2c) mem2 (seg_rom trbsegs))) in HJ2. reshok_bx HS 23%nat.
idtac "MEMSET1 OK".
stretch cx lp HS HJ2 SHOK AG HE8 HE2 HE60 HE21 HBg HBld [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 336, z_sp cx - 304)]
ltac:(awr2 cx lp AG HE8 HE2 HE60 Actx HBg Ald HBld) HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
mcall cx HS HJ2 AG HE33 HE25 HE2 HE3 HE4 Hzgp Hztp (z_lm cx) 8192 0x8bd4c HBlm Alm.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff2 & Hfr2 & Hpres3).
reseat HS HJ3 HP3 [0; 1]%nat AG ltac:(keptR AG HE8 HE2 Hfr2 Hpres3 HSEP 2%nat).
mpost cx Heff2 Hfr2 (z_lm cx) 8192 ZLM HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 0x8bd4c) mem3 (seg_rom trbsegs))) in HJ3. reshok_bx HS 23%nat.
idtac "MEMSET2 OK".
stretch cx lp HS HJ3 SHOK AG HE8 HE2 HE60 HE21 HBg HBld [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 336, z_sp cx - 304)]
ltac:(awr2 cx lp AG HE8 HE2 HE60 Actx HBg Ald HBld) HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
mcall cx HS HJ3 AG HE34 HE25 HE2 HE3 HE4 Hzgp Hztp (z_lc cx) 4096 0x8bd6c HBlc Alc.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff3 & Hfr3 & Hpres4).
reseat HS HJ4 HP4 [0; 1]%nat AG ltac:(keptR AG HE8 HE2 Hfr3 Hpres4 HSEP 3%nat).
mpost cx Heff3 Hfr3 (z_lc cx) 4096 ZLC HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 0x8bd6c) mem4 (seg_rom trbsegs))) in HJ4. reshok_bx HS 23%nat.
idtac "MEMSET3 OK".
stretch cx lp HS HJ4 SHOK AG HE8 HE2 HE60 HE21 HBg HBld [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 336, z_sp cx - 304)]
ltac:(awr2 cx lp AG HE8 HE2 HE60 Actx HBg Ald HBld) HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
mcall cx HS HJ4 AG HE35 HE25 HE2 HE3 HE4 Hzgp Hztp (z_li cx) 8192 0x8bd8c HBli Ali.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff4 & Hfr4 & Hpres5).
reseat HS HJ5 HP5 [0; 1]%nat AG ltac:(keptR AG HE8 HE2 Hfr4 Hpres5 HSEP 4%nat).
mpost cx Heff4 Hfr4 (z_li cx) 8192 ZLI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 0x8bd8c) mem5 (seg_rom trbsegs))) in HJ5. reshok_bx HS 23%nat.
idtac "MEMSET4 OK".
stretch cx lp HS HJ5 SHOK AG HE8 HE2 HE60 HE21 HBg HBld [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 336, z_sp cx - 304)]
ltac:(awr2 cx lp AG HE8 HE2 HE60 Actx HBg Ald HBld) HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo Rg2 Hldceil Hlp0 Hlpc.
idtac "RUN5 OK".
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 304)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv21 : ew Ev 23 = Z_to_bv 64 SB) by (rewrite (AG 23%nat) by lia; exact HE21);
assert (HEv25 : ew Ev 25 = Z_to_bv 64 (z_idl cx)) by (rewrite (AG 25%nat) by lia; exact HE25);
assert (HEv1 : ew Ev 1 = raw) by (rewrite (AG 1%nat) by lia; exact HE1)
end.
rreg HS (1%bv : bv 5) R1.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W7 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
lazymatch goal with |- exists r2 m2 d2, {| cfg_ms := mkst (ms_regs ?msF) _ (ms_mem _) _; cfg_model := ?dd |} = _ /\ _ =>
exists (ms_regs msF), (ms_mem msF), dd end.
split. { cbn [ms_regs]. rewrite R1. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia.
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. rewrite HEv1. unfold YK0s.ret_ok in Hraw. rewrite Hraw. reflexivity. }
split. { apply (ajournal_materialize trbsegs B LAWS Hsegs). exact HJ5. }
split.
{ lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia] end. }
split.
{
pose proof HFX as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P25 & P3 & P4).
apply aregs_preserved_eqs;
first [ let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = _ => rewrite (AG n) by lia; rewrite HE0; apply ew_Ereg_nat; reflexivity end
| let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?(AG 8%nat), ?(AG 23%nat) by lia; rewrite ?HE8, ?HE21, ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
symmetry; first [exact P9 | exact P23 | exact P18 | exact P19 | exact P20]
| match goal with |- ?g => idtac "AREGS_PRESERVED" g end ]. }
split. { rreg HS (24%bv : bv 5) R26. rewrite R26. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia.
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. rewrite (AG 24%nat) by lia. rewrite HE0. apply ew_Ereg_nat. reflexivity. }
split.
{
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HRg end.
cbn [ms_mem restrict] in HRg.
lazymatch type of HRg with region_ok _ ?Ex _ _ =>
assert (G8 : bv_unsigned (ew Ex 8) = z_ctx cx) by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HEv8; apply unsigned_lit_small; lia) end.
eapply (agen_at_of_ptrs _ _ _ (lp + 1) (z_idl cx + 2) 1);
[ exact HG
| intros a Ha; apply HK; [lia | unfold rd_untouched, rd_written, z_tisz; septac HSEP 0%nat 6%nat; septac HSEP 1%nat 6%nat; septac HSEP 2%nat 6%nat; septac HSEP 3%nat 6%nat; septac HSEP 4%nat 6%nat; lia]
| | | ];
[ change 4%nat with (N.to_nat 4); eapply (field_of_region _ _ 8%nat (z_ctx cx) _ _ _ _ _ 60 4%N _ (lp + 1) HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?HE41, ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia ]
| change 2%nat with (N.to_nat 2); eapply (field_of_region _ _ 8%nat (z_ctx cx) _ _ _ _ _ 64 2%N _ (z_idl cx + 2) HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?HEv25, ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ]
| change 2%nat with (N.to_nat 2); eapply (field_of_region _ _ 8%nat (z_ctx cx) _ _ _ _ _ 66 2%N _ 1 HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ] ]. }
split.
{ eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply HK; [lia|]. unfold rd_untouched, rd_written, z_tisz.
septac HSEP 5%nat 6%nat. septac HSEP 0%nat 5%nat. septac HSEP 1%nat 5%nat. septac HSEP 2%nat 5%nat. septac HSEP 3%nat 5%nat. septac HSEP 4%nat 5%nat. lia. }
split; [exact ZTI|]. split; [exact ZLM|]. split; [exact ZLC|]. split; [exact ZLI|].
exact HK.
Qed.
End S.
End d.
