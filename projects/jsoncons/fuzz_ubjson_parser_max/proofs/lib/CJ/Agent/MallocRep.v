(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocRep () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep.CEIL_WRAP_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."; "stdpp.option."], [["1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1id"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2True"; "2and"]; ["2eq"; "2not"; "2or"; "3N"; "3Z"; "4write_to_mem"; "0RUNp"; "6b8"; "6lr_lo"; "6wz"; "7W_high"; "7sh_ticks"; "7shadow_le"; "7ticks_ok"; "5actives"; "5area_rep"]; ["5b8"; "5group_rep"; "5pw"; "5shadow_rep"; "5wz"; "8upd"; "9disjoint_from"; ":le2"; ":sx32"; ":wa"; ":zx16"; ":zxb"; ";alloc_ceiling"; "<AREA_HDR"; "<Known"; "<META_SIZE"]; ["<NSLOTS"; "<RKBrk"; "<RKGroup"; "<aadd"; "<aptr"; "<aptr_eqb"; "<area"; "<cell_read"; "<cellval"; "<conc"; "<get_meta_rec"; "<get_shadow"; "<ghdr"; "<hav_add"; "<havoc_pages"; "<havoc_units"]; ["<meta"; "<mkShadow"; "<mstate"; "<optr"; "<r_base"; "<r_cells"; "<r_hav"; "<r_havp"; "<r_kind"; "<r_len"; "<region"; "<rkind"; "<round_up_pg"; "<s_regions"; "<s_shadow"; "<s_tick"]; ["<set_active"; "<set_tick"; "<shadow"; "<shadow0"; "<size_class"; "<stale"; "<wr8"; "=In"; ">le"; "?add"; "?b2z"; "?div"; "?land"; "?ldiff"; "?le"; "?lt"]; ["?modulo"; "?mul"; "?of_nat"; "?pow"; "?shiftr"; "?sub"; "?testbit"; "?to_nat"; "0W"; "0a"; "0ar"; "0b"; "0bs"; "0c"; "0cells"; "0ch"]; ["0cov"; "0d"; "0g"; "0gh"; "0hav"; "0havp"; "0hi"; "0hl"; "0i"; "0k"; "0lo"; "0m"; "0n"; "0o"; "0off"; "0p"]; ["0p0"; "0p1"; "0pg"; "0q"; "0r"; "0rid"; "0sc"; "0sh"; "0st"; "0st'"; "@insert"; "@is_Some"; "@lookup"; "AZ_to_bv"; "Abv"; "Abv_signed"]; ["Abv_swrap"; "Abv_unsigned"; "Abv_wrap"; "BN_countable"; "BZ_countable"; "Cmap_insert"; "Dgmap"; "Dgmap_lookup"; "Dgmap_partial_alter"; "Eeq_dec"; "Feq_dec"; "Gfrom_option"; "0t"; "0tc"; "0u"; "0v"]; ["0x"; "0y"; "0z"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition b8 (z : Z) : byte := Z_to_bv 8 z.
Definition pw (st : mstate) (p : optr) : word := wz (oconc st p).
Definition meta_word (mr : meta) : Z :=
m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr.
Definition meta_cells (st : mstate) (mr : meta) : list cell :=
[C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (pw st (m_mem mr));
C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))].
Definition brk_word (st : mstate) : Z :=
match c_brk (ctx st) with
| BrkUntried => 0
| BrkDead => 2^64 - 1
| BrkLive rid off => conc st (rid, off)
end.
Definition ctx_head_cells (st : mstate) : list cell :=
let c := ctx st in
[C8 (wz (c_secret c)); C4 (wz (c_init_done c)); C4 (wz (c_mmap_counter c));
C8 (pw st (c_free_meta_head c)); C8 (pw st (c_avail_meta c));
C8 (wz (c_avail_meta_count c)); C8 (wz (c_avail_meta_area_count c)); C8 (wz (c_meta_alloc_shift c));
C8 (pw st (c_meta_area_head c)); C8 (pw st (c_meta_area_tail c)); C8 (pw st (c_avail_meta_areas c))].
Definition actives (st : mstate) : list word := map (fun i => pw st (active st (Z.of_nat i))) (seq 0 48).
Definition usages (st : mstate) : list word := map (fun i => wz (usage st (Z.of_nat i))) (seq 0 48).
Definition unmap_seqs (st : mstate) : list byte := map (fun i => b8 (unmap_seq st (Z.of_nat i))) (seq 0 32).
Definition bouncess (st : mstate) : list byte := map (fun i => b8 (bounces st (Z.of_nat i))) (seq 0 32).
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Definition ctx_tail_cells (st : mstate) : list cell :=
[C1 (b8 (c_seq (ctx st))); CB 7 (zeros 7); C8 (wz (brk_word st))].
Definition lr_lo (r : region) : Z :=
match r_kind r with RKBrk => r_base r + 4096 | _ => r_base r end.
Lemma lr_lo_ge : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "9'R:&RN&R4r1%211&H%113%6231pX:81").
Proof. intros r. unfold lr_lo. destruct (r_kind r); lia. Qed.
Lemma lr_lo_group : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "A'R:'@'R;&R8r1%211(QB%63521'D&Hr2%211&R4%113%=3631p081pX:@1").
Proof. intros r. unfold lr_lo. intros ->. reflexivity. Qed.
Lemma lr_lo_nbrk : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "C'R:&A'@'R;&R8r1%211(QA%63521%811'D&Hr2%211&R4%113%>3631p081pX:B1").
Proof. intros r. unfold lr_lo. destruct (r_kind r); congruence. Qed.
Section MREP.
Variable st : mstate.
Variable m : word -> option byte.
Definition area_rep (a : aptr) (ar : area) : Prop :=
rw_cells asegs m (conc st a) [C8 (wz (a_check ar)); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
/\ (forall k, 0 <= k < NSLOTS ->
rw_cells asegs m (conc st a + AREA_HDR + META_SIZE * k)
(meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
/\ rw_cells asegs m (conc st a + 4064) [CB 32 (zeros 32)].
Definition mrep_areas : Prop :=
forall a ar, (s_areas st) !! a = Some ar -> area_rep a ar.
Definition group_rep (b : aptr) (gh : ghdr) : Prop :=
exists w8 : byte,
rw_cells asegs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
/\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Definition mrep_groups : Prop :=
forall b gh, (s_groups st) !! b = Some gh -> group_rep b gh.
Definition shadow_rep (rid : N) (r : region) : Prop :=
wr_at asegs m (r_base r) (round_up_pg (r_len r))
/\ forall o v, 0 <= o < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) o = Known v ->
bytes_at asegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Definition mrep_shadow : Prop :=
forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> shadow_rep rid r.
End MREP.
Definition blocks_preserved (L : list (Z * Z)) (m m' : word -> option byte) : Prop :=
forall a, (exists bl, In bl L /\ fst bl <= a < fst bl + snd bl) -> m' (wa a) = m (wa a).
Lemma conc_aadd : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q4'R2';'C'D%3221&T;'R:&T<'TF&TI&TC%349215&TG%14;437&4r2%23>=1&R=r3%211%=6B>9741%@2?1'@&QIr4&QC%128;%4231&RI%625;%221?%93L41p0;1pW4N1pX0N1pXBQ31").
Proof.
intros st [rid off] d [r Hr]. unfold conc, aadd, get_region. cbn. rewrite Hr. lia.
Qed.
Lemma conc_region : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q7'R2'C'D'R:'@'9%113&T<'TF&TI&TC%34:218&TG%14<43:r3&R=r4%211%;6A?7541(0r1%22B1%B3@41&QIr5(:%14IH:<%4231&RI&R4r2%211%421B%M3O61p0<1pX:Q01pWNQ21pX<Q41pXBQ61").
Proof. intros. unfold conc, get_region. cbn. rewrite H. reflexivity. Qed.
Lemma round_up_pg_ge : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "7'D&RNr1&R<%112%4231pZ261").
Proof. intros. unfold round_up_pg, PGSZ. assert (0 <= Z.land (-x) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. Qed.
Lemma wz_unsigned : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "G'D'?&RNzr1%3221&RO&S3+2+R0%3221%5271%;271'@&TAyR0&Ir2%211%5241%73D13p091pZ2F1").
Proof. intros x. intros. unfold wz. apply unsigned_lit. lia. Qed.
Lemma b8_unsigned : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "D'D'?&RNzr1%3221&RO+X0%2241%8241'@&TAy8&Gr2%211%5241%73A13p091pZ2C1").
Proof. intros x. intros. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.
Lemma zxb_b8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "H'D'?&RNzr1%3221&RO+X0%2241%8241'@'T>yR0%211&Q;&Gr2%211%411&I%114%;3831p0=1pZ2G1").
Proof. intros x. intros. unfold zxb, wz. rewrite b8_unsigned by lia. reflexivity. Qed.
Lemma zx16_wz : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "F'D'?&RNzr1%3221&RO+RPP0%2241%8241'@'T>yR0%211&Q:&Ir2%211%411%93612p0;1pZ2E1").
Proof. intros x. intros. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_wz : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "I'D'?&RNzr1%3221&RO&S3+2+O%3221%5271%;271'@'T>yR0%211&Q8&Ir2%211%411%93612p0;1pZ2H1").
Proof. intros x. intros. unfold sx32, wz. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.
Lemma land_ldiff_distr : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "?'D'@&RLr3&RMr2r1%3221%6251%7264%6214%:3;31pVH<1pVD=1pZ2>1").
Proof. intros x a b. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.
Lemma land_pgmask : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "J'D'?&RNzr1%3221&RO&S3+2+R0%3221%5271%;271'@&RLr2+_ooooooooolP0%3221&S5&S0+TP0%2261%4271%:3G61p0<1pZ2I1").
Proof. intros x.
intros Hx.
assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
rewrite land_ldiff_distr. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.
Lemma mod_mod_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "I'D'?&RNzr2%3221r1%5231%7231'@&S0r4&S3+2%221:%5241r3%5241%8231%9282%;3D21p0=1pVHF1pVDG1pZ6H1").
Proof. intros z a b. intros. apply Z.mod_mod_divide. exists (2^(b-a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
Lemma swrap32_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "?'D'@&S0&T@yQ0r1%3221&S3+2+Q0%3221%9251%:272%<3=21pZ6>1").
Proof. intros z.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
replace (z + 2^31 - 2^31) with z by lia. reflexivity.
Qed.
Lemma wrap32_sx32_wz : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "L'D'?&RNzr1%3221&RO&S3+2+Q0%3221%5271%;271'@&TByQ0&TAyR0&Q8&Ir2%211%411%7261%:291%<3I15p0>1pVDK1").
Proof. intros a.
intros Ha. unfold sx32, wz. rewrite (unsigned_lit a) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32).
rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite swrap32_mod32. apply Z.mod_small. lia.
Qed.
Lemma bit_test_form : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "O'D&RNzr2%3221'@&RL&S0&T@yQ0&S4r4r3%3221%6251&S3+2+R0%3221%<251+1%?221&RJ&S6%12=<%311%E3J51p0G1p0H1pWBM1pVDN1").
Proof. intros a i.
intros Ha Hi. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
rewrite Z.testbit_spec' by lia. rewrite <- Z.shiftr_div_pow2 by lia.
rewrite (mod_mod_pow2 _ 1 64) by lia.
rewrite <- (mod_mod_pow2 (bv_swrap 32 (a ≫ i)) 1 32) by lia. rewrite swrap32_mod32.
rewrite (mod_mod_pow2 _ 1 32) by lia. reflexivity.
Qed.
Lemma signed_wz_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "G'D'?&RNzr1%3221&RO&S3+2+QO%3221%5271%;271'@&T?yR0&T=r2%2231%5241%73D13p091pZ2F1").
Proof. intros x.
intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
End CEIL_WRAP_1.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Section SE.
Local Abbreviation SEC_T_size_class_range := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "D'D'?&RNzr1%3221&RO+Q@%2241%8241+1&RDr2%211%<241+WoO%>231%@231p091pX>C1")) (only parsing).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_size_class_range) 0%nat 0%nat).
Lemma size_class_range : ltac:(sec_stmt2 constr:(SEC_T_size_class_range) 1%nat 0%nat).
Proof.
intros H. unfold size_class.
assert (F : Forall (fun x => 1 <= x <= 8191) size_classes).
{ unfold size_classes. repeat (constructor; [lia|]). constructor. }
apply (Forall_nth (fun x => 1 <= x <= 8191) size_classes); [exact F|]. cbn. lia.
Qed.
End SE.
Definition get_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 gw : word) (off16 idx : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2 a4,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) a2 (Z_to_bv 64 4096) a4 gw (Z_to_bv 64 0x1a000) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs).
Lemma conc_region' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q8'R2&QD'R:'@'9%113&T<'C'TF&TI&TC%344219&TG%14643;&4'Dr2%33:21&R=r3%211%?6>C:841(0r1%22F1%F3D41&QIr4%2219&RI&R4%11?&<%13JB>%5231%Q03D71p0;1pX:Q31pX8Q51pXBQ71").
Proof. intros st [rid off] r H. apply conc_region. exact H. Qed.
Definition meta_slot (st : mstate) (g : aptr) : Prop :=
exists a ar k, (s_areas st) !! a = Some ar /\ 0 <= k < NSLOTS /\ g = aadd a (AREA_HDR + META_SIZE * k).
Lemma le2_lohi : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q7'D'?&RNzr2%3221&RO+X0%2241%8241'@'7'T>y8%211%411&Q7&Q4&RIr4&S1r3%22?1%5241%711%911(2&Q0%119%218(8%11A%63B31%73C51%H3C91p0J1p0K1pW>Q51pWFQ61").
Proof.
intros lo hi Hl Hh. unfold le2, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
f_equal; [apply Z_to_bv8_mod; rewrite <- Zplus_mod_idemp_r; replace (256 * hi) with (hi * 2^8) by lia; rewrite Z_mod_mult; rewrite Z.add_0_r; reflexivity|].
f_equal. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
replace (lo + 256 * hi) with (lo + hi * 256) by lia. rewrite Z.div_add, Z.div_small by lia. reflexivity.
Qed.
Definition ticks_ok (st : mstate) : Prop :=
(forall rid sh u hl ch, (s_shadow st) !! rid = Some sh -> (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
/\ (forall rid sh pg t, (s_shadow st) !! rid = Some sh -> (r_havp sh) !! pg = Some t -> (t <= s_tick st)%N).
Definition wr_in (st : mstate) (rid : N) (a len : Z) : Prop :=
exists r, (s_regions st) !! rid = Some r /\ lr_lo r <= a /\ a + len <= r_base r + round_up_pg (r_len r) /\ 0 <= len.
Lemma area_rep_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "QL'R2'T>yR0%211'9y8%511%311p051&QD'QF'@'D&QIr5r1%3221r6%5213%83731pX0;1'?&RNz%2219&RO&Q@%22<1%7241'R0&QJr7&QC&RI&Q=&S1&Q?r2%3221%6251%82J1%;2:1r8%=213%Q13?31p0A1pWDQ21&Or4r3%34CQ421%44DQ2Q53p021p071p0Q21pVFQ=1pVDQ?1pWHQA1pXDQJ1pXBQK1").
Proof.
intros st st' m a ar Hconc Hm (H1 & H2 & H3).
assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
unfold area_rep. rewrite !Hconc, Hpw. split; [exact H1|]. split; [|exact H3].
intros k Hk. rewrite Hmc, Hm by exact Hk. apply H2. exact Hk.
Qed.
Lemma group_rep_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q2'R2'T>yR0%211'9y8%511%311p051&QD'QL'@'D&QIr5r1%3221r6%5213%83731pX0;1&Q1r4r3r2%448321%549<43p021p081pW8C1pVHE1pWHG1pXDQ01pXBQ11").
Proof.
intros st st' m b gh Hconc (w8 & H1 & H2).
assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
exists w8. rewrite Hconc, Hpw. auto.
Qed.
Lemma shadow_rep_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q0'R2'T>yR0%211'9y8%511%311p051'C'R:'@'RB&QKr4r2%3221r5%5213%83731&Q3r6r3%342918%4437:2p021p071pX:A1pX<C1pWHE1pXDN1pXBO1").
Proof. intros st st' m rid r Hs [H1 H2]. split; [exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.
Lemma group_rep_frame : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "QO'R2'T>yR0%211'9y8%511%311p051'D'7%115&QD'QL&RNzr4%3221&RIr5&S2&6%12@6%311%6251&S3+2+R0%3221%?251'B&QIr8%221A+9%A221r6%G221%A2Q0C%C11%F241%K218%<251&Q1r9%241=JMr:&E&Q9%11Ar7%43721%9461@Q1p081p0<1p0J1p0Q71pW8Q<1pVHQ>1pVJQ@1pVDQC1pWHQE1pXBQN1").
Proof.
intros st m a bs b gh A0 A1 D (w8 & H1 & H2). exists w8. split; [|exact H2].
apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
Qed.
Lemma shadow_rep_frame : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "R3'R2'T>yR0%211'9y8%511%311p051'D'7%115'C'R:&RNzr4%3221&RIr5&S2&6%12@6%311%6251&S3+2+R0%3221%?251'B&R4r3%211&R<&R9%114%311%D251r6%J221%D2Q3F%F11%I241%N21;%?251&Q3r9r8%3421NQ1r:&E&Q9%115r7%43821%:461AQ5p081p0=1p0N1p0Q;1pX:Q@1pX<QB1pVJQD1pVDQG1pWHQI1pXBR21").
Proof.
intros st m a bs rid r A0 A1 D [HW HB]. split; [apply wr_at_write; exact HW|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Hb Hv]. split; [|exact Hv].
apply bytes_at_write_other; [exact Hb|lia|lia|cbn; lia].
Qed.
Lemma s_shadow_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "QI'R2&QD'D'@'TF'C&TI&TC'RB%544321&R>&RFr2r1r3%43321%611&T:&TE&TH%14?>=<%34@=<1&4%13BE;(R1';%12HE&TJ&TD%I4K213%;4L324%=4M521&<%13LOE(:&RL+WO%22H1&R?%11I%64Q6Q331&R5&QK%12MD%311%L7Q;C@><51&R6%114&R7%116%J3531%Q91Q5%Q37Q?Q<Q;OM21%QB3Q<Q51pZ0QD1pX0QF1pXBQH1").
Proof. intros. reflexivity. Qed.
Lemma get_shadow_unfold : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "J'R2'C'@'RB&QKr2r1%3221&TK&5%117&RC&T<'TF&TI&TC%34?21=&TG%14A43?&R>%11?%96DB53?1%>5CC<;1%E3D@1pX<G1pXBI1").
Proof. reflexivity. Qed.
Lemma get_shadow_wr8_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "QA'R2&QD'D'@'RB&QK&RFr2r1r3%43321&4'C%231;6%9241(R1&T:';%12@6'TF&TJ&TD%34D214&TE&TH%14G547%34H841&<%13@JE(:&RL+WO%22H1&R?%11I%64Q1G31&R5%Q02LH%211%G7Q5EA=;41&R6%114&R7%116%M3531%Q:3Q9O1pZ0Q<1pX0Q>1pXBQ@1").
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_eq. reflexivity. Qed.
Lemma get_shadow_wr8_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "L'R2';'C'D%3221&A'@r1&4r3%23871%53941%711'RB&QK&RFr4r5%33291r2%6221%7242%@3921p0;1pX<F1pZ0F1pX0F1pXBK1").
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma cell_read_wr8_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q1'R2';'C'D%3221&A'@r1&<r3%23871%53841%711'QH&QG&QK&RFr4r5%332:1&4%13CB4%7231r2%:221%:274%<213%E3>31p0@1pWLJ1pZ0K1pX0K1pXBQ01").
Proof. intros. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma cell_read_wr8_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q6'R2&QD'D&Mr3%211'?&RNzr2%3221&RO+X0%2241%8241'@'QH&QG&QK&RFr4r5%332B1&4'C%231G5%8241&<%134J8%<231(Q>%11K%A3@31p0C1p0M1pZ0Q11pX0Q31pXBQ51").
Proof.
intros st p v [T1 T2] Hv. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_eq.
replace (Z.land v 255) with v by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
unfold get_shadow. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn.
- assert (SP : stale_pg (r_havp sh !! (snd p `div` 4096)) (Some (s_tick st)) = false).
{ unfold stale_pg. destruct (r_havp sh !! (snd p `div` 4096)) eqn:E2; [|reflexivity].
apply N.ltb_ge. eapply T2; eauto. }
assert (SU : stale (default [] (r_hav sh !! (snd p `div` 16))) (snd p `mod` 16) (Some (s_tick st)) = false).
{ unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([cov t] & Hin & Hb).
destruct (r_hav sh !! (snd p `div` 16)) eqn:E3; cbn in Hin; [|contradiction].
apply Bool.andb_true_iff in Hb. destruct Hb as [_ Hb]. apply N.ltb_lt in Hb.
pose proof (T1 _ _ _ _ _ E E3 Hin) as HT. cbn [snd] in HT. exfalso. apply (N.lt_irrefl t). eapply N.le_lt_trans; [exact HT | exact Hb]. }
rewrite SP, SU. reflexivity.
- rewrite lookup_empty. cbn. reflexivity.
Qed.
Lemma ticks_ok_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "?'R2&QD'D&Mr3%211&RFr2r4%33521%711p061pZ0:1pX0<1pXB>1").
Proof.
intros st p v [T1 T2]. split.
- intros rid sh u hl ch Hs Hu Hin. cbn [s_tick wr8 upd_shadow set_shadow] in *.
rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
+ rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hu.
unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hu.
* eapply T1; eauto.
* rewrite lookup_empty in Hu. discriminate.
+ rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
- intros rid sh pg t Hs Hp. cbn [s_tick wr8 upd_shadow set_shadow] in *.
rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
+ rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hp.
unfold get_shadow in Hp. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hp.
* eapply T2; eauto.
* rewrite lookup_empty in Hp. discriminate.
+ rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.
Lemma wr8_mod : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "A'R2&QD'D'@&RFr2r1r3%43321&S0+X0%2251%83715%:3=51pZ0<1pX0>1pXB@1").
Proof.
intros. unfold wr8, upd_shadow. cbn beta.
replace (Z.land (v mod 256) 255) with (Z.land v 255); [reflexivity|].
change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma le2_split : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q5'D'?&RNzr1%3221&RO+RPP0%2241%8241'@'7'T>y8%211%411&Q7&Q4r2%211%411(2&Q0&S0+X0%2271%411&RK%12:4%711(8%11A%;3B31%<3C71%H3C>1p0J1pZ0Q41").
Proof.
intros v Hv. replace v with (v mod 256 + 256 * (v / 256)) at 1 by (pose proof (Z.div_mod v 256); lia).
rewrite le2_lohi; [reflexivity| |]; [pose proof (Z.mod_pos_bound v 256); lia | split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]].
Qed.
Lemma get_meta_rec_upd : forall st g f g',
get_meta_rec (upd_meta g f st) g' = if aptr_eqb g' g then f (get_meta_rec st g) else get_meta_rec st g'.
Proof.
intros. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn [s_metas set_metas].
unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.
Lemma aptr_eqb_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "9&QD'@'1&QEr1%2211(=%63521pW681").
Proof. intros [a b]. unfold aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.
Lemma map_seq_upd : forall {X} (f g : nat -> X) (j : nat) (x : X) n s,
(forall i, (s <= i < s + n)%nat -> g i = if Nat.eqb i j then x else f i) ->
(s <= j)%nat ->
map g (seq s n) = upd (map f (seq s n)) (j - s) x.
Proof.
intros X f g j x n. induction n as [|n IH]; intros s Hg Hj; [reflexivity|].
cbn [seq map]. destruct (Nat.eq_dec j s) as [->|NE].
- rewrite Nat.sub_diag. cbn [upd]. rewrite Hg by lia. rewrite Nat.eqb_refl. f_equal.
apply map_ext_in. intros i Hi. apply in_seq in Hi. rewrite Hg by lia.
destruct (Nat.eqb_spec i s); [lia|reflexivity].
- replace (j - s)%nat with (S (j - S s)) by lia. cbn [upd]. f_equal.
+ rewrite Hg by lia. destruct (Nat.eqb_spec s j); [lia|reflexivity].
+ apply IH; [intros; apply Hg; lia|lia].
Qed.
Lemma active_set_active : forall st sc v i,
active (set_active sc v st) i = if Z.eqb i sc then v else active st i.
Proof.
intros. unfold active, set_active, upd_ctx. cbn [ctx s_ctx c_active set_active_map].
destruct v as [p|]; destruct (Z.eqb_spec i sc); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
- rewrite lookup_delete_eq. reflexivity.
- rewrite lookup_delete_ne by congruence. reflexivity.
Qed.
Lemma actives_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q4'R2'D&R3'?&RNzr2%3221&RO+Q@%2241%8241'@'7'T>yR0%211%411&N&R@r3r4%332@1%511&Q5%714&S7%117&Q2%128G%64>531%C3>81p0E1pZ0O1pX>Q11pXBQ31").
Proof.
intros st sc v Hsc. unfold actives.
replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
apply (map_seq_upd (fun i => pw st (active st (Z.of_nat i))) (fun i => pw (set_active sc v st) (active (set_active sc v st) (Z.of_nat i)))); [|lia].
intros i Hi. rewrite active_set_active.
assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
rewrite Hpw. destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.
Definition sh_ticks (sh : shadow) (t : N) : Prop :=
(forall u hl ch, (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
/\ (forall pg t', (r_havp sh) !! pg = Some t' -> (t' <= t)%N).
Definition shadow_le (sh sh' : shadow) : Prop :=
r_cells sh' = r_cells sh /\ forall o v, cell_read sh' o = Known v -> cell_read sh o = Known v.
Lemma shadow_le_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "5'RB&Lr1%2211pX@41"). Proof. intros; split; auto. Qed.
Lemma shadow_le_trans : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "<'RB&Lr3r2%3221r5%5214p031p041pVL91pVH:1pVD;1").
Proof. intros a b c [E1 H1] [E2 H2]. split; [congruence|]. eauto. Qed.
Lemma In_filter_bool : forall {A} (f : A -> bool) (l : list A) x,
In x (filter (fun y => f y) l) <-> In x l /\ f x = true.
Proof.
intros A f l x. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
unfold Is_true. destruct (f x); intuition congruence.
Qed.
Lemma stale_hav_add : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q8'7';'D'C%3221%511'9%114&RGr1r6%33721&RH&<r2%23=<1r5%5221p071pW0?1'@'1&RE&QMr4%2391?r3%5321=(3%93821r7%93175%<3;14p041p0?1pYLL1pVHQ21pYJQ21pW2Q41pW@Q21").
Proof.
intros hl cov t b tc Ht Hs. unfold stale in *.
apply Bool.not_true_iff_false. apply Bool.not_true_iff_false in Hs. rewrite existsb_exists in *.
intros ([c' h'] & Hin & Hb). apply Hs. cbn [fst snd] in Hb.
apply Bool.andb_true_iff in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1.
destruct (Z.ltb_spec cov c').
- exists (c', h'). split; [|cbn [fst snd]; rewrite (proj2 (Z.ltb_lt _ _) Hb1), Hb2; reflexivity].
unfold hav_add. right. apply In_filter_bool. split; [exact Hin|]. cbn. apply Z.ltb_lt. assumption.
- exists (cov, t). split; [unfold hav_add; left; reflexivity|]. cbn [fst snd].
rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
destruct tc as [tc|]; [|reflexivity]. apply N.ltb_lt. apply N.ltb_lt in Hb2.
pose proof (Ht _ Hin) as Hh. cbn [snd] in Hh. eapply N.lt_le_trans; [exact Hb2|exact Hh].
Qed.
Lemma hav_unit_step : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "QG'TF'D&TJ&TD';'C%2251%746541'7%113%:49871%;4:986&K(R1r6r5r4%43321r1%7221'?&Lr7%:3198&T:&TE&TH%14JIHB%34KCB1&QMr3r2&TK&5%11I(8%11N&T<&TG%14Q6Q5Q4N%36Q7ON1HJ%95Q0Q0751%=3<;1%C7Q:Q2Q1?K1M%O3F1M%H2F1%Q222?%K221p0M1pYJQ<1pW2QA1pYNQB1pW<Q91pW:Q;1pVNQ?1").
Proof.
intros cells hav havp u cov t [T1 T2]. cbn [r_hav r_havp] in T1, T2.
assert (Hl : forall ch, In ch (default [] (hav !! u)) -> (snd ch <= t)%N).
{ intros ch Hin. destruct (hav !! u) eqn:E2; cbn in Hin; [eapply T1; eauto| contradiction]. }
split.
- split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
destruct (Z.eq_dec (o / 16) u) as [E|NE].
+ rewrite E, lookup_insert_eq in Hc. cbn [default from_option id] in Hc. rewrite E.
destruct (cells !! o) as [[v0 tc]|].
* destruct (stale_pg (havp !! (o / 4096)) (Some tc)) eqn:SP; [cbn in Hc; discriminate|].
destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) (Some tc)) eqn:SU; [cbn in Hc; discriminate|].
rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
* destruct (stale_pg (havp !! (o / 4096)) None) eqn:SP; [cbn in Hc; discriminate|].
destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) None) eqn:SU; [cbn in Hc; discriminate|].
rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
+ rewrite lookup_insert_ne in Hc by congruence. exact Hc.
- split; cbn [r_hav r_havp]; [|exact T2].
intros u' hl ch Hu Hin. destruct (Z.eq_dec u' u) as [->|NE].
+ rewrite lookup_insert_eq in Hu. inversion Hu; subst hl. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
apply In_filter_bool in Hin. destruct Hin as [Hin _]. apply Hl. exact Hin.
+ rewrite lookup_insert_ne in Hu by congruence. eapply T1; eauto.
Qed.
Lemma hav_page_step : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q9'TF'D&TJ&TD';'C%2251%746541'7%113%:49871%;4:986&K(R1r5r4r3%43321r1%7221'?&Lr6%:3198&T:&TE&TH%14JIHF%34KGA1r2%67MIC2>1?%B39A1%;291%E224%>221p0@1pYJO1pX6Q41pW<K1pW:M1pVNQ11").
Proof.
intros cells hav havp pg t [T1 T2]. cbn [r_hav r_havp] in T1, T2. split.
- split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
destruct (Z.eq_dec (o / 4096) pg) as [E|NE].
+ rewrite E, lookup_insert_eq in Hc. rewrite E.
destruct (cells !! o) as [[v0 tc]|]; cbn [stale_pg orb] in Hc.
* destruct (N.ltb_spec tc t); [discriminate|].
destruct (havp !! pg) as [h|] eqn:E2; cbn [stale_pg].
-- pose proof (T2 _ _ E2). replace (tc <? h)%N with false by (symmetry; apply N.ltb_ge; lia). exact Hc.
-- exact Hc.
* discriminate.
+ rewrite lookup_insert_ne in Hc by congruence. exact Hc.
- split; cbn [r_hav r_havp]; [exact T1|].
intros pg' t' Hp. destruct (Z.eq_dec pg' pg) as [->|NE].
+ rewrite lookup_insert_eq in Hp. inversion Hp; subst. lia.
+ rewrite lookup_insert_ne in Hp by congruence. eapply T2; eauto.
Qed.
Lemma Z_iter_invariant : forall {A} (f : A -> A) (Inv : A -> Prop) n x,
(forall y, Inv y -> Inv (f y)) -> Inv x -> Inv (Z.iter n f x).
Proof.
intros A f Inv n x Hf Hx. destruct n; cbn; auto. apply Pos.iter_invariant; auto.
Qed.
Lemma havoc_units_le : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q7'TF'D&TJ&TD';'C%2251%746541'7%113%:49871%;4:986&K(R1r6r5r4%43321r1%7221'?&Lr7%:3198&QOr3r2%34;21=%?361=%8261%B224%;221p0=1pYJL1pZ4Q11pZ2Q21pW<I1pW:K1pVNO1").
Proof.
intros cells hav havp x y t T. unfold havoc_units.
set (f := fun acc : Z * gmap Z (list (Z * N)) => _).
apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells (snd acc) havp)
/\ sh_ticks (mkShadow cells (snd acc) havp) t)).
- intros [u h] [HL HT]. unfold f. cbn [fst snd].
destruct (hav_unit_step cells h havp u (if u =? (y - 1) / 16 then (let r := y mod 16 in if r =? 0 then 16 else r) else 16) t HT) as [HL2 HT2].
split; [eapply shadow_le_trans; eauto| exact HT2].
- cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.
Lemma havoc_pages_le : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "Q7'TF'D&TJ&TD';'C%2251%746541'7%113%:49871%;4:986&K(R1r6r5r4%43321r1%7221'?&Lr7%:3198&QNr3r2%34;21<%?36>1%8261%B224%;221p0=1pYJL1pX4Q11pX2Q21pW<I1pW:K1pVNO1").
Proof.
intros cells hav havp p0 p1 t T. unfold havoc_pages.
set (f := fun acc : Z * gmap Z N => _).
apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells hav (snd acc))
/\ sh_ticks (mkShadow cells hav (snd acc)) t)).
- intros [pg h] [HL HT]. unfold f. cbn [fst snd].
destruct (hav_page_step cells hav h pg t HT) as [HL2 HT2].
split; [eapply shadow_le_trans; eauto| exact HT2].
- cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.
Lemma sh_ticks_of_ticks_ok : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "?'R2'C&Mr2%211&K&QKr3%2215&R?%113%6231p081pX<<1pXB>1").
Proof.
intros st rid [T1 T2]. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
- split; [intros; eapply T1; eauto | intros; eapply T2; eauto].
- split; cbn; intros; rewrite lookup_empty in *; discriminate.
Qed.
Lemma shadow_rep_le : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "O'R2'T>yR0%211'9y8%511%311p051'C'R:&L&QKr5r2%3221r4%5213%7231&Q3r6r3%342618%443:72p021p071pX:@1pX<B1pWHD1pXDM1pXBN1").
Proof. intros st st' m rid r [_ HL] [HW HB]. split; [exact HW|]. intros o v Ho Hc. apply HB; auto. Qed.
Definition W_high (W : list (Z * Z)) : Prop := forall lo hi, In (lo, hi) W -> alloc_ceiling <= lo.
Lemma W_high_disjoint : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "I'7';'D%2211%411&Jr3%211&RN&RIr2%2251&Q<vF%211%7241&Q6r5r4%3321=p051p0>1pWJD1pVDE1pVBD1").
Proof.
induction W as [|[lo hi] W IH]; intros a n HW Hn; cbn; [exact I|].
split. { left. pose proof (HW lo hi ltac:(left; reflexivity)). lia. }
apply IH; [| exact Hn]. intros lo' hi' Hin. apply (HW lo' hi'). right; exact Hin.
Qed.
Lemma ticks_ok_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "C'R2'C&RH&R?r2%211r1%5221&Mr3%211&RAr4%2241%611p051p091pYJ@1pXBB1").
Proof.
intros st t Ht [T1 T2]. split; cbn.
- intros rid sh u hl ch H1 H2 H3. pose proof (T1 rid sh u hl ch H1 H2 H3). lia.
- intros rid sh pg t' H1 H2. pose proof (T2 rid sh pg t' H1 H2). lia.
Qed.
Definition unlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a0 (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs).
Lemma malloc_impl_spec_statement : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "1'>"). Proof. exact I. Qed.
Lemma free_trivial_spec_statement : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "1'>"). Proof. exact I. Qed.
Lemma wrappers_spec_statement : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocRep "1'>"). Proof. exact I. Qed.
End CEIL_WRAP_2.
