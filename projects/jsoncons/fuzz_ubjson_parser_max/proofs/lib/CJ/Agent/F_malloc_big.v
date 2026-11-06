(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocFacts_A MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp AllocSlot_iface F_malloc_join F_malloc_core MallocHINV.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A2 F_malloc_bigw.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_malloc_big () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_bigw."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0C"; "1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3N"]; ["3Z"; "0RUNp"; "4big_meta"; "4big_ml"; "5ticks_ok"; "6brk_link_ps"; "6mem"; "6pres_except"; "7grp_hdr_cov"; "7unk_agree"; "8mmap_addr_ok"; "9ivl"; "9munch"; "9outside"; ":wa"; ";alloc_ceiling"]; ["<BrkLive"; "<IB"; "<RKGroup"; "<UNIT"; "<Unknown"; "<aptr"; "<area"; "<brkstate"; "<c_brk"; "<c_mmap_counter"; "<cell_read"; "<cellval"; "<conc"; "<ctx"; "<get_meta_rec"; "<get_shadow"]; ["<get_stride"; "<ghdr"; "<is_err"; "<mctx"; "<meta"; "<mkGhdr"; "<mmap_answer_ok"; "<mstate"; "<r_base"; "<r_kind"; "<r_len"; "<ranges_free"; "<region"; "<rkind"; "<round_up_pg"; "<s_areas"]; ["<s_groups"; "<s_next_rid"; "<s_regions"; "<s_reserved"; "<s_slots"; "<shadow"; "<u32"; "=PState"; "=neg_errno"; ">add"; ">div"; ">le"; ">lt"; ">modulo"; ">mul"; ">pow"]; [">sub"; "0W"; "0a"; "0c"; "0e"; "0g"; "0h"; "0hi"; "0len"; "0live"; "0lo"; "0m"; "0m'"; "0n"; "0o"; "0off"]; ["0q"; "0r"; "0rid"; "0s"; "0st"; "0st'"; "0st3"; "0stF"; "0stM"; "?insert"; "?lookup"; "@bv"; "AN_countable"; "AZ_countable"; "Aprod_countable"; "Bprod_eq_dec"]; ["Cmap_insert"; "Dgmap"; "Dgmap_lookup"; "Dgmap_partial_alter"; "Eeq_dec"; "Feq_dec"; "0x"; "0xa"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition big_final (st3 : mstate) (g : aptr) (rid : N) (n : Z) : mstate :=
let needed := n + IB + UNIT in
let st4 := upd_meta g (fun mr =>
m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
(m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.
Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).
Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).
Lemma bf_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big ";'<'QD&Q>vS7vRE%3221&BvS2vRM%3221%:3951").
Proof.
unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
rewrite G0. reflexivity.
Qed.
Lemma bf_meta_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "A&Q5&='<r1vRE%33521%511'QD&Q>vS7r2%3221vS6%5213%<3731p091pV2@1").
Proof. intros q.
intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma bm_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big ";'<'QD&Q>vS8vRE%3221&BvS2vRM%3221%:3951").
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma bm_meta_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "A&Q5&='<r1vRE%33521%511'QD&Q>vS8r2%3221vS6%5213%<3731p091pV2@1").
Proof. intros q.
intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma bf_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "='<'SA'?&SD&S<'QL%544321&R2vS7%211vS6%411%<3631"). Proof. reflexivity. Qed.
Lemma bf_areas : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "E'<'SA&Q5&S?'?&SD'@&SE%544321&S>&S<&S=%36872651'Q6%=4<621&QOvS7%211vS6%411%D3631"). Proof. reflexivity. Qed.
Lemma bf_reserved : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "<'<'5'9'@%2211%411&R3vS7%211vS6%411%;3631"). Proof. reflexivity. Qed.
Lemma bf_next : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "8'<'?&R1vS7%211vS6%411%73631"). Proof. reflexivity. Qed.
Lemma bf_groups : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "Q6'<'SA&Q5&S?'?&SD'@&SE%544321&S>&S<&S=%36872651'QA%=4<621&R0vS7%211&S9'9%12@>&S@&SC%14E?;:%344;:1(8vS2z%34HF21(QE(1vRE%22N1%4216vS6%D11%B7@GF<831%Q53GD1").
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
rewrite GN. reflexivity.
Qed.
Lemma bm_groups : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "Q6'<'SA&Q5&S?'?&SD'@&SE%544321&S>&S<&S=%36872651'QA%=4<621&R0vS8%211&S9'9%12@>&S@&SC%14E?;:%344;:1(8vS2z%34HF21(QE(1vRE%22N1%4216vS6%D11%B7@GF<831%Q53GD1").
Proof. reflexivity. Qed.
Lemma bf_shadow : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big ";'?'<'R5&Q?vS7r1%3221vS8%5213%83731pV2:1").
Proof. intros q. reflexivity. Qed.
Lemma bf_shadow_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "A'?&='<r1vS2%33521%511'R5&Q?vS7r2%3221vS6%5213%<3731p091pV2@1").
Proof. intros q.
intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma bf_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "8'<'QC&Q=vS7%211vS8%411%73631").
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
Lemma bf_counter : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big ">'<'@&Q9&Q=vS7%211%411&R6&R9vRC+1%3221%511%=3<71").
Proof. rewrite bf_ctx. reflexivity. Qed.
Lemma ticks_ok_big_final : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "6&DvS8%211vS7%411p031").
Proof. intros H; exact H. Qed.
Lemma bf_stride : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "A'<'@&Q@&BvS2vRM%3221%511&R@&R>&C%116+TP0%4221+@%7221%@3?91").
Proof.
unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.
Lemma bf_slots : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "Q4'<'SA&Q5&S?'?&SD'@&SE%544321&S>&S<&S=%36872651'9%12<8%>4=731&R4vS7%211&S9%72@>&S@&SC%14E?;9%344:91(8vS2+@%34HF21vREz%64MI21vS6%A11%?7>DC:631%Q33DA1").
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.
Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^32 ->
malloc_core full_lay st1 n =
SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
if is_err r then ret (st1, None) else
let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
alloc_meta (step_seq st2) (fun st3 go =>
match go with
| None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
| Some g => ret (big_final st3 g rid n, Some (g, 0))
end) (ret (st1, None))).
Proof.
intros Hn. unfold malloc_core.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
reflexivity.
Qed.
Lemma unk_agree_transfer : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "SI'QG&F'S;yR0%211'7y8%511%311pW>51&Ir5r3r2%43321'?'QL'<%=12&S:'SA&SD&S<%348217&SB%14:439&R2r7%211%:6>=64@1(1r1%22@1%@3?41'QM&QI%11G(Q2%E3421'>';r4r:%A11%I6MLEC31%?2MQ1%M3L21'R5&Q?r9%2219%329:%Q33521'@&Hr;%231Q=Ir6%4331Q=p031pV071&R;z%221QB&R<&QN&QJ%11QH%311%52QH1%N271'Q;&Q:r=%J21Q?%321QO(Q4%11R0%QM3731&=r8%K381Q8%311&N&R9&QH%116%321R<%511%Q211r<%113%R;3RD31p0;1p0@1p0I1pU>Q;1pV0Q<1%QJ2Q61%QK2Q?1%QL2QF1%QE2;R:%N21RJ%RF3Q01Jp01Gp0Q31pU>QE1pV0QF1%R5281p0R71p0R=1pV4RO1pV6S11%S73QHS6S5p021p0S51pUJS;1pUHSD1pUNSE1pV<SG1pV:SH1").
Proof. intros st st' o m m'.
intros UA H rid r off h Hr Hk Ho Hc NG.
destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
- rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
- exfalso. apply NG. eapply NEW; eauto.
Qed.
Lemma grp_hdr_cov_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "Q1'QG'?'@'<'SA&Q5&S?&SD&SE%348271&S>&S<&S=%36<62;51'QA%;4:621&R0r3%211r4%411%B3631&Hr5r2%33281%43379p021p071pV0K1pV6M1pV<O1pV:Q01").
Proof. intros st st' rid off. intros EG (b & gh & Hb & E & R). exists b, gh. rewrite EG. auto. Qed.
Lemma munmap_answer_ok_range a : match a with RgErr e => 1 <= e <= 4095 | RgDone _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
destruct a as [e|b]; cbn [range_val]; intros He.
- unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (2 ^ 64 - e =? 0); reflexivity.
- reflexivity.
Qed.
Lemma mmap_answer_ok_err : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "Q1'5'9'@%2211%411';&R;+1r1%3221+SoO%5231%7231'<'2&QFvAr4r3&R8r2%211%746541(:%;3:21&QB%115%>3=14%G241p0A1pU:L1pUBM1pUDL1").
Proof. intros live len e.
intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
- replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- apply Z.ltb_lt. lia.
Qed.
Lemma mmap_answer_ok_addr : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "QH'5'9'@%2211%411&R;zr2%3221'<'2&JvAr3(6%11<%544319(:%93821&QFr5r4%34:219%>3=16';&R<%12D5&R=+TP0%2281%E3L1H&R9&QN%11=%32=1&O%11H%Q0231&QKr6%231C7%Q03O1H&QB%11F(4%Q43Q321%F251%G2:1%H2B1%I2G1p0K1p0Q11p0Q<1pW@QC1pUBQD1pUDQC1").
Proof. intros live len xa.
intros L0 A B. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. destruct A as [[[A1 A2] A3] _].
apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
pose_ceil. change page_size with 4096 in A1.
unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
assert (NE : is_errno_form xa = false).
{ unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; pose_ceil; lia). reflexivity. }
destruct B as [B|B]; [rewrite NE in B; discriminate|].
rewrite !Bool.andb_true_iff in B. destruct B as [[[_ _] _] B4].
repeat split; auto. unfold is_err, TWO64. apply Z.ltb_ge. pose_ceil. lia.
Qed.
Lemma brk_link_ps_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "Q;'QG'R7'<'Q7&Q8&Q=r2%211%411r3%511%711%:3941'?'@r6%;11%=11(Q0r1%22>1%C3B41&Q<(8%14;:?B%32:1r7%5213%J3>31p081pV0@1pV6B1&Er5%221Ir4%4231p031p071p0K1pV8Q71pV<Q91pV:Q:1").
Proof. intros st st' s.
intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
rewrite (EC rid off eq_refl). exact BL.
Qed.
Lemma munch_of_pointwise : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "QJ'@&F&R;zr4%3221&R?+2+R0%3221%8261';r1%;2:1&R<%1236%5231'>r2r8%6221r7%D214%6231'<'7'S;y8%211%411r6&Nr3%211%411%>12%<3721p0>1p0F1pU6Q71&L(3'9%12Q;Q;(8%14Q=Q=H?(6%114%73531r5%:321Q>p0<1p0Q:1p0Q@1pUJQE1pUHQF1pU@QH1pUFQI1").
Proof. intros lo hi m m'.
intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.
Lemma pres_except_of_munch_nw : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "QA'@!pW>21'5&K%211'S;yR0%211'7y8%511%311p051&Lr3r2r1%43321';&R;z%2215&R<&R?+2+R0%3221%52;1%:271&=r7%11@%311&M%124Dp031p081pU6Q61&Gr6r4%3321Kp051p0J1pUJQ01pUHQ11pU4Q:1p2Q>1").
Proof. intros C W m m'.
intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. unfold wview. rewrite E. auto.
Qed.
Lemma cell_read_hh0 st rid off : (s_shadow st) !! rid = None -> 0 <= off ->
cell_read (get_shadow (hdr_havoc (rid, 0) st) rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
destruct (Z.eq_dec (off / 16) 0) as [E|NE].
- rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
- rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.
Lemma round_up_pg_4115 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "H'@&R;zr1%3221'<&QN&R9r2&Q1%3221&Q3%5221%711&R>&R:+TPC%:291+TP0%4221%6212%@3E81p0B1pULG1").
Proof. intros n. intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.
Lemma big_stride : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_big "Q2'@'?';&R;zr2%3221&R<&R?+2+Q0%3221%5271%;271'<&Q@&Br3%22=1%411&R@&QN&R9&Q1%2271&Q3%4221%611+@%9221%@3N;1p0B1pV6O1pULQ11").
Proof. intros n rid. intros Hn. rewrite bf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.
End CEIL_WRAP_1.
