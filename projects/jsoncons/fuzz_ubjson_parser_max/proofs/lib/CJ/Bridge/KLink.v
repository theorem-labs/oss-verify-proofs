(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import Prelim Monad STree Malloc Prog KInv KStep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_KLink () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.KLink.CEIL_WRAP_1.KL2DEF."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"]; ["2not"; "2or"; "3map"; "4Z"; "0L"; "0L'"; "5VmMaps"; "5alloc_top"; "5iv_subtract"; "5live_bytes"; "5map_contains"; "5map_has"; "5map_remove"; "5maps_subtract"; "5mkVmMapsFull"; "5region_free"]; ["5sp_window_lo"; "5vm_brk"; "5vm_init_sp"; "5vm_limit"; "5vm_maps"; "5vm_mmap_base"; "5vm_noaccess"; "5vm_reserved"; "5vm_start_brk"; "0M"; "0P"; "0R"; "0RUNp"; "6KL2"; "6phase_inv2"; "7mmap_len"]; ["8alloc_ceiling"; "9BPDead"; "9BPGuard"; "9BPLive"; "9BPQueried"; "9BPUntried"; "9MAPFX"; "9answer_ok"; "9brk_phase"; "9brk_quiet"; "9bump_meta"; "9edisj"; "9ehi"; "9elo"; "9event_post"; "9g_remove"]; ["9lbrk_pages_ok"; "9ld_brk"; "9ld_brkreg"; "9ld_groups"; "9ld_metas"; "9ld_resv"; "9lranges"; "9mled"; "9pwdisj"; "9set_brkph"; "9set_live"; "9vmwf"; "9wcov"; "9went"; ":EBrk"; ":EMmap"]; [":EMprotect"; ":EMunmap"; ":PGSZ"; ":PROT_NONE"; ":PROT_RW"; ":brk0_answer_ok"; ":cptr"; ":mmap_fixed_answer_ok"; ":mprotect_answer_ok"; ":munmap_answer_ok"; ":round_up_pg"; ";In"; ";NoDup"; ";filter"; "<add"; "<le"]; ["<lt"; "<modulo"; "<mul"; "<of_nat"; "<pow"; "<sub"; "0a"; "0aw"; "0b"; "0br"; "0cur"; "0e"; "0e'"; "0e0"; "0e1"; "0e2"]; ["0f"; "0h"; "0h'"; "0hi"; "0k"; "0l"; "0l0"; "0l1"; "0l2"; "0len"; "0lo"; "0m"; "0maps"; "0maps'"; "0ms"; "0n"]; ["0nw"; "0p"; "0pbrk"; "0pbrk'"; "0ph"; "0r"; "0req"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0sz"; "0v"; "0x"; "0y"]]).
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma pwdisj_In : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "K'6':'T8yR0%211%4211%611'R8r3%211&RKr4%23741r5%43961'A'>%13<46&QK%1268%5231p071p0:1p0>1pW0C1pVND1pW<D1").
Proof.
induction l as [|e l IH]; intros e1 e2 Hp H1 H2; [destruct H1|].
inversion Hp; subst. destruct H1 as [<-|H1], H2 as [<-|H2].
- left; reflexivity.
- right. apply H3. exact H2.
- right. pose proof (H3 _ H1) as D. unfold edisj in *. lia.
- apply IH; assumption.
Qed.
Lemma region_free_app_r : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "J'6':'T8yR0%211%4211%611'>'2&O&1r4r3%33821r2r1%73321(<%;3:21%:3875%=3<13p031pX0B1pV>C1pWBB1pW@C1").
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|]. cbn in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.
Lemma region_free_disj : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q7'6':'T8yR0%211%4211%611'>'2&Or4r3r2%43321(<%83721&RKr5%23=61'A&RO&RN&T9%12D6%22E>%4221&QM%11@%8231&QL%11C%;218%=241p0?1p0C1pVHN1pX0Q01pV>Q11pWJQ01").
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.
Lemma vmwf_cons : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q>'6':'T8yR0%211%4211%611&R;r3%211'=&S0&T9%12:5&RNr2%42=1%3241%7251&RO&S4+2+R0%3221%5271%?271'>'2&Or5r4%3321G(<%73621(3(9%14Q0Q076r6%43Q121%Q011p071p0@1p0Q11pX0Q71pV>Q81pWJQ71").
Proof.
intros maps a n [Hb Hp] Hn Hrf. split.
- intros e [<-|Hin]; [unfold elo, ehi; cbn; lia| apply Hb; exact Hin].
- constructor; [|exact Hp]. intros e' Hin. pose proof (region_free_disj _ _ _ _ Hrf Hin). unfold edisj, elo, ehi in *. cbn. lia.
Qed.
Lemma pwdisj_filter : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "D':'T8yR0%211%4211'2p021'6%114'R8r1%211&RMr3r2%33;21%711p061pW<:1pW2=1").
Proof.
induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
- constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
- apply IH; assumption.
Qed.
Lemma vmwf_remove : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "A'6':'T8yR0%211%4211%611&R;r2%211&Lr3%2214%611p051pV>;1pWJ:1").
Proof.
intros maps a [Hb Hp]. unfold map_remove. split.
- intros e Hin. apply List.filter_In in Hin as [Hin _]. auto.
- apply pwdisj_filter. exact Hp.
Qed.
Lemma iv_subtract_sub : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "QD'T8yR0%211'C':%1233&S0z&T9r4%2291%5241&RO&RNr6%72>1r5%92@1%5231&S4+2+R0%3221%;251&RKr3&Hr7%241><C%53H41'=r8%H2O1&QM%11I%G231&QL%11L%N2Q5;%J271%L231%Q3274%<221%=281p0?1p0F1p0Q31pVHQ:1pW8Q=1pWFQ>1pXFQ@1pV>QA1").
Proof.
intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz).
unfold bv_modulus in *.
apply in_app_or in Hin as [Hin|Hin].
- destruct (Z.ltb_spec (bv_unsigned a) (lo)); [|destruct Hin].
destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
- destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.
Lemma maps_subtract_In : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q4'6':'T8yR0%211%4211%611'C&RKr1&Mr4r3r2%43321%73:61'?'=r6%;3>:1&H&4%13BB=&;%13DD?r5%64421?%C3F?1%;291qVLH1%>2I1p0@1pVHK1pW8J1pWFK1pWJM1").
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
- exists (a, sz). split; [left; reflexivity| exact Hin].
- destruct (IH _ _ _ Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0| exact H1].
Qed.
Lemma iv_subtract_disjoint : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "QF'T8yR0%211'C'=&S0&T9r4%2271&RNr3%52:1%3241%8251&RO&S4+2+R0%3221%5271%@271r2%A2<1'Ar6%C2H1r5%E2J1%C231%?21F%@2D5%8221'>'6':%12Q1Q1%311&Hr7%241?=Q0(3(9%14Q8Q84B(7%119%53:31%>3:71p0@1p0J1p0M1pW8Q?1pWFQ@1pXFQB1pV>QC1").
Proof.
intros a sz lo hi Hwf Hlh Hd. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). unfold bv_modulus in *.
destruct Hd as [Hd|Hd].
- replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
cbn. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
- replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
cbn. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma maps_subtract_keep : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q8'6':'T8yR0%211%4211%611'C&R;r4%211&S0r3%2241&RKr6%23;41'A&RO&QL%11;%3216r5&QM%11?%7231%9251&Mr8r7%3321?%A3J91p061p0A1p0E1p0I1pVHO1pW8N1pWFO1pWJQ11").
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
- left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
+ specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
+ unfold elo, ehi in Hd. cbn in Hd. lia.
- right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.
Lemma iv_subtract_contains : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "R:'T8yR0%211'C&S0r4r3%3221&ROzr5%3221&RN&T9r8%22>1r7%42@1%6231&S4+2+R0%3221%?251r9%<2H1%B21@r6%H21Br;%A2M1r:%C2O1%E231%J271'A%L2D5%M2=G%3221'?':%12Q7Q7'=&RKr1&Hr>r=r<%44321D%73961&QM%118%Q=21F&QL%11;%Q@2Q01%?241%@281qVHB1%E2C1p0G1p0L1p0Q31p0Q61p0Q:1p0QG1p0QL1pXLR11pXJR21pW8R31pWFR41pXFR61pV>R71").
Proof.
intros a sz lo hi x y Hlh Hlo Hwf Hax Hxy Hy Hd. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
destruct Hd as [Hd|Hd].
- replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
eexists. split; [apply in_or_app; left; left; reflexivity|]. unfold elo, ehi; cbn. rewrite unsigned_lit by lia. lia.
- replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
eexists. split; [apply in_or_app; right; left; reflexivity|]. unfold elo, ehi; cbn. rewrite !unsigned_lit by lia. lia.
Qed.
Lemma maps_subtract_In_intro : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q1'6':'T8yR0%211%4211%611'C&RKr2r5%33621&H&4r3%23;;1&;%13==3r4%744291%<3?;1&Mr7r6%3321>%A3D;1p061p0@1pVJG1pVHH1pW8G1pWFH1pWJJ1").
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi e e' Hin H'; [destruct Hin|].
cbn. apply in_or_app. destruct Hin as [<-|Hin]; [left; exact H'| right; eapply IH; eauto].
Qed.
Lemma pwdisj_app : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "N'6':'T8yR0%211%4211%611'R8r2%211&RKr6%23741&QKr4r3%3221p051p061pX<>1pX4?1&1r5%23B19%A11p051p0A1p0B1pRHF1pRFG1").
Proof.
induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
- intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
- apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.
Lemma iv_subtract_pwdisj : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q5'T8yR0%211'C&S0r2r1%3221&ROzr3%3221&RN&T9r6%22>1r5%42@1%6231&S4+2+R0%3221%?251'R8&Hr7r4%342><1%511p071p0D1p0I1pW8N1pWFO1pXFQ11pV>Q21").
Proof.
intros a sz lo hi Hlh Hlo Hwf. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
destruct (Z.ltb_spec (bv_unsigned a) (lo)); destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); cbn [app].
- constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
- constructor; [intros e' []| constructor].
- constructor; [intros e' []| constructor].
- constructor.
Qed.
Lemma vmwf_subtract : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "N'6':'T8yR0%211%4211%611'C&S0r2r1%3221&ROzr3%3221&R;r5%211&Mr6r4%33251%711p061p0:1p0?1pW8D1pWFE1pWJG1").
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi Hlh Hlo [Hb Hp]; [split; [intros e []| constructor]|].
inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
specialize (IH lo hi Hlh Hlo Hwf'). destruct IH as [IHb IHp].
assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
cbn. split.
- intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
- apply pwdisj_app; [apply iv_subtract_pwdisj; [exact Hlh| exact Hlo| lia]| exact IHp|].
intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.
Lemma wcov_mono : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "K'6':'T8yR0%211%4211%611'C&RKr1r5%33621r2%53813p031pVH:1&R<r3%23816r4%43:13p031p071pW8@1pWFA1pWLC1pWJD1").
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.
Section KL2DEF.
Variable resv_img : list (word * word).
Variable img_hi : Z.
Record KL2 (L : mled) (pbrk : Z) (h : VmMaps) : Prop := mkKL2 {
k2_wf : vmwf (vm_maps h);
k2_nabnd : forall e, In e (vm_noaccess h) -> elo e < ehi e <= 2^64;
k2_resv : ld_resv L = map wwZ (vm_reserved h);
k2_resv_img : vm_reserved h = resv_img;
k2_resv_top : forall e, In e (vm_reserved h) -> ehi e <= bv_unsigned (vm_start_brk h);
k2_start : 0 < bv_unsigned (vm_start_brk h)
/\ bv_unsigned (vm_start_brk h) mod PGSZ = 0
/\ bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h)
/\ bv_unsigned (vm_start_brk h) + 4 * PGSZ <= alloc_ceiling
/\ img_hi <= bv_unsigned (vm_start_brk h);
k2_groups : forall b l, In (b, l) (ld_groups L) ->
0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
/\ In (went b (mmap_len l)) (vm_maps h) /\ brk_disj L b (mmap_len l);
k2_metas : forall b l k, In (b, l, k) (ld_metas L) ->
0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
/\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
/\ In (went b (mmap_len l)) (vm_maps h) /\ brk_disj L b (mmap_len l)
/\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
exists e, In e (vm_noaccess h) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
k2_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
k2_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
/\ wcov (vm_maps h) (b + PGSZ) (b + l);
k2_phase : match ld_brk L with
| BPUntried => vm_brk h = vm_start_brk h /\ ld_brkreg L = None
| BPQueried cur => cur = bv_unsigned (vm_start_brk h)
/\ bv_unsigned (vm_brk h) = cur /\ pbrk = cur /\ ld_brkreg L = None
| BPGuard cur => cur = bv_unsigned (vm_start_brk h)
/\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
/\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
/\ (exists e, In e (vm_maps h) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
/\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
/\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
| BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk h) = b + l /\ pbrk = b + l
| BPDead => True
end;
k2_isp : bv_unsigned (vm_init_sp h) = alloc_ceiling + 2 ^ 23 }.
Ltac k2_open HK := destruct HK as [Kwf Kna Kresv Kimg Krt Kstart Kgr Kme Kdis Kreg Kph Kisp].
Definition phase_inv2 (ph : brk_phase) (L : mled) (pbrk : Z) (h : VmMaps) : Prop :=
match ph with
| BPUntried => vm_brk h = vm_start_brk h /\ ld_brkreg L = None
| BPQueried cur => cur = bv_unsigned (vm_start_brk h)
/\ bv_unsigned (vm_brk h) = cur /\ pbrk = cur /\ ld_brkreg L = None
| BPGuard cur => cur = bv_unsigned (vm_start_brk h)
/\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
/\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
/\ (exists e, In e (vm_maps h) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
/\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
/\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
| BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk h) = b + l /\ pbrk = b + l
| BPDead => True
end.
Lemma KL2_rephase : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "I'R7'QH'C'F'Q=r5r3r1%43321&Q>r6r2%347261&R9r7%2251r4%=321;p061p0;1pW4A1pX8C1pX6D1pX:F1pQ:H1").
Proof. intros L ph pbrk pbrk' h K Hph. k2_open K; constructor; cbn; auto. Qed.
Lemma KL2_dead : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "C'R7'C'F'Q=r4r3r1%43321&R9(QAr5%3221r2%:3281p071pW4=1pX8?1pX6@1pQ:B1").
Proof. intros. eapply KL2_rephase; [eassumption| exact I]. Qed.
Lemma KL2_set_live : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "E'R7'6&RF%211'C'F'Q=r4r2r1%43321&R:r5%2261r3%93217p061pW4<1pX6>1pXH@1pQ:D1").
Proof. intros L v pbrk h K. k2_open K; constructor; cbn; auto. Qed.
Lemma elo_pair : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "@'T8yR0%211'>'C&QM(9r2r1%347721%511&T9%12;5%:3931pX0<1pV>=1"). Proof. reflexivity. Qed.
Lemma ehi_pair : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "C'T8yR0%211'>'C&QL(9r2r1%347721%511&RN&T9%12<6%22=6%4221%=3<61pX0?1pV>@1"). Proof. reflexivity. Qed.
Lemma went_In_bounds : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "R9'R7'C'F'Q=r5r4r3%43321'A&RK':%12::(9r2%24==81&R3r6%211%93741'?%:29C%94DD@?r1%;4<F21&R4r7%211%B3741qW:K1%:2L1%F2<1'=&S0z%221M&Q?%11N%5241&RO&RN%12Q34&Q@vQ<%211%6241'T8yR0%211%Q6211&R=%12Q=>&Q4%11Q@%Q<3531'>&QM%116%33QH1QD&QL%119%63QK1D%N241%O291%Q02C1%Q12K1%Q22O1p0Q41p0QL1pW<R31pVBR41pW4R41pX6R61pQ:R81").
Proof.
intros L pbrk h b l K Hin. pose proof alloc_ceiling_lt.
assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps h)) as (Hl & Hb & Hc & Hm).
{ destruct Hin as [Hin|[k Hin]]; [pose proof (k2_groups _ _ _ K _ _ Hin)| pose proof (k2_metas _ _ _ K _ _ _ Hin)]; tauto. }
pose proof (mmap_len_ge l ltac:(lia)). splits; auto; try lia.
- apply elo_went. lia.
- apply ehi_went; lia.
Qed.
Lemma In_lranges : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "R<'R7':'C%2211&RKr1&R6r2%211%53641'A&R5r3%211%:3;71'?'=(9%14@@;=&R3r5%211%B3C41'>r4&RJ%11E%:4IID1%53I41%=271qW<L1%@2M1qVBN1%B2O1%Q12OQ0%B4Q1Q1GL%C4Q1Q21O&R4r6%211%Q43641%@1Q2%I4Q8Q8N1%D3Q8G1%L241qW:Q;1%O2Q<1qW<Q=1%Q12Q>1qVBQ?1%Q32Q@1'8%11QA&R2%11Q2(0%12QEQ6%Q23531&RN&RB%22QE1&S5%12Q43%Q>4QMQM31%Q93QMQ81%QA281qW<R01%QD2R11qVBR21%QF2R31%QL2D1%QM2Q61%QN2QJ1p0R01pXJR71pQ:R;1").
Proof.
intros L x Hin. unfold lranges in Hin. rewrite !in_app_iff in Hin. destruct Hin as [H|[H|[H|H]]].
- left; exact H.
- right; left. apply in_map_iff in H as ([b l] & <- & H). exists b, l. auto.
- right; right; left. apply in_map_iff in H as ([[b l] k] & <- & H). exists b, l, k. auto.
- right; right; right. destruct (ld_brkreg L) as [[b l]|]; [|destruct H]. destruct H as [<-|[]]. exists b, l. auto.
Qed.
Section SE.
Local Abbreviation SEC_T_KL2_lbrk_pages_ok := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "RG'R7'C'F'Q=r5r4r3%43321&S0z%2214&RO&RN%1298&Q@vQ<%211%6241'>'2&O&1':'T8yR0%211%4211&Q7r7%211&Q4%113%;3631&T7r6%22;1%32<Q0%A3521(<%E3D21'8%C2Q8Q8%211&R2r<%211(0(9r2r1%34QAQA21%52:1%Q23:71'=&S1&RB%2281%Q73QH1Q@'A%Q?2QE;r:%QB221r9%QC231%QD2QJ9%QF221%8251%>2:1p0@1pW<R41pVBR51&R0r;r8%34QK21Q>%QI3QH1Q5p061p0Q61p0QM1p0R51p0R61p0R:1pWDRA1pWFRB1pW4RB1pX6RD1pQ:RF1")) (only parsing).
Variable L : ltac:(sec_ty2 constr:(SEC_T_KL2_lbrk_pages_ok) 0%nat 0%nat).
Variable pbrk : ltac:(sec_ty2 constr:(SEC_T_KL2_lbrk_pages_ok) 1%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_KL2_lbrk_pages_ok) 2%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_KL2_lbrk_pages_ok) 3%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_KL2_lbrk_pages_ok) 4%nat 0%nat).
Lemma KL2_lbrk_pages_ok : ltac:(sec_stmt2 constr:(SEC_T_KL2_lbrk_pages_ok) 5%nat 0%nat).
Proof.
intros HK Hlo Hlen Hceil Hrf Hbrk.
pose proof alloc_ceiling_lt as Hcl.
assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
{ destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
- rewrite (k2_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ulo, Ulen in D. exact D.
- injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
- injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
- injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.
End SE.
Lemma wcov_rf_disj : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q?'6':'T8yR0%211%4211%611'C&R<r5r4r3%43321'>'2&Or6r2%33271(<%73621&S0z&T9%12E=%4231r7%621;'A&RO&RN%82L?%92MG%3221r8%6221%72:5%9221p0;1p0>1p0D1p0M1pX2Q61pV@Q71pW8Q51pWFQ61pWJQ81").
Proof.
intros maps lo hi aw nw Hc Hrf Hn Hlh.
destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
destruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr).
pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.
Lemma mmap_len_pos_pg : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "='C&S0zr1%3221&RO&RB&Q?r2%211%5241p071pW<<1").
Proof.
intros l Hl. pose proof (mmap_len_ge l Hl). pose proof (mmap_len_aligned l).
pose proof (Z_div_mod_eq_full (mmap_len l) 4096). unfold PGSZ. nia.
Qed.
Lemma KL2_brk0 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q7'R7'C'F'Q=r3r2r1%43321'>'QH&R1r4%211(QE%63521&T9yR0&Q1%11>%4231'='2&RE%11A(<%A3421&R9(QD%11Fr6%4221%L31ID%<271tX<Q0>1p0D1p0L1pW4Q21pX6Q41pQ:Q61").
Proof.
intros L pbrk h HK Hph r.
pose proof (k2_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
pose proof (bv_unsigned_in_range 64 (vm_brk h)) as R. unfold bv_modulus in R.
subst r. rewrite Ebrk in *. split.
- unfold brk0_answer_ok, TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl.
rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- eapply KL2_rephase; [exact HK|]. cbn [phase_inv2]. rewrite Ebrk. splits; auto.
Qed.
Section SE.
Local Abbreviation SEC_T_KL2_mmap_new := (forall L pbrk h (a : word) len (isnone : bool), KL2 L pbrk h -> brk_quiet L -> 0 < len < LEN_MAX ->
let n := mmap_len len in
bv_unsigned a mod PGSZ = 0 -> 0 < bv_unsigned a -> bv_unsigned a + n <= alloc_ceiling ->
region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true ->
let h' := mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h)
(if isnone then (a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
KL2 (if isnone then set_metas ((bv_unsigned a, len, 0) :: ld_metas L) L else set_groups ((bv_unsigned a, len) :: ld_groups L) L) pbrk h'
/\ mmap_answer_ok (lranges L) len (bv_unsigned a) = true /\ is_err (bv_unsigned a) = false) (only parsing).
Variable L : ltac:(sec_ty2 constr:(SEC_T_KL2_mmap_new) 0%nat 0%nat).
Variable pbrk : ltac:(sec_ty2 constr:(SEC_T_KL2_mmap_new) 1%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_KL2_mmap_new) 2%nat 0%nat).
Lemma KL2_mmap_new : ltac:(sec_stmt2 constr:(SEC_T_KL2_mmap_new) 3%nat 0%nat).
Proof.
intros aw len isnone HK Hq Hlen n A1 A2 A3 Hrf h'.
pose proof alloc_ceiling_lt as Hcl.
set (a := bv_unsigned aw) in *.
pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
assert (Ua : aw = Z_to_bv 64 a) by (subst a; symmetry; apply Z_to_bv_bv_unsigned).
assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
a + n <= b0 \/ b0 + mmap_len l0 <= a).
{ intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Un in D. exact D. }
assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
{ intros b0 l0 E. pose proof (k2_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Un in D. exact D. }
split; [|split].
2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. unfold PGSZ in A1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
enough (a + n <= lo \/ lo + m <= a) as D.
{ destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
- rewrite (k2_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Un in D. exact D.
- injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
- injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
- injection E as -> ->. pose proof (k2_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
{ intros Hin. apply in_app_or in Hin as [Hin|Hin].
- apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
- apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
k2_open HK.
assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
phase_inv2 (ld_brk L') L' pbrk h').
{ intros L' E1 E2. unfold phase_inv2. rewrite E1, E2. subst h'. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
destruct (ld_brk L); try contradiction; auto. }
destruct isnone; constructor;
first [ apply (Hph' (set_metas _ L)); reflexivity
| apply (Hph' (set_groups _ L)); reflexivity
| subst h'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
- apply vmwf_cons; [exact Kwf| rewrite Un; lia| exact Hrfm].
- intros e [<-|He]; [rewrite elo_pair, ehi_pair, Un; subst a; lia| apply Kna; exact He].
- intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
- intros b0 l0 k [E|Hin].
+ injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
* left; unfold went, KInv.wz; rewrite <- Ua; reflexivity.
* exact Dbrk.
* intros q Hq1 Hq2. exists (aw, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Un. fold n in Hq2. subst a. lia.
+ specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
- cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
- intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
- apply vmwf_cons; [exact Kwf| rewrite Un; lia| exact Hrfm].
- intros b0 l0 [E|Hin].
+ injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
* left; unfold went, KInv.wz; rewrite <- Ua; reflexivity.
* exact Dbrk.
+ specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
- intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
- cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
- intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_KL2_brk_grow1 := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "T6'R7'C'F'Q=r4r3r2%43321'>'QH&R1r5%211(QD%118%73631'T8yR0%211&Q1%11@&RN&RJ%11C&S2+2&RB%3221%7251'=&T9%12>I%H3OE1r7%J3Q11Gr1%?259%M3Q421&S1%128=z%Q13Q821&S0%123<&S4+R0%22E1%52;1&RO&Q8r6%211%F2Q31%521A&@%Q?3QFD?%211'2&QGvQ<r8(R>%11K%54431QD(<%QI3821&QN%1375QH%R131QIB%Q8241&O&1':%12QGQG&Q7%11I&Q4%11K%73531&T7%12QOQE%;33R;1%R:3I1B%QE2R2R>%QO21QI&Q@%11K%Q7231r:%L1RD%Q04O21RE%RC3Q21K%J343RG(N%D1Q2(3(9%14R?R?RMA%F1Q6%43J21&Q6%11Q9%QE1Q:%R92RFS3%RC21R=%J2RH1&Q3%11Q?&Q5%11QA&Q2%11QC%C8B=;:7531%S>3ES<1%RE2G1p0L1p0Q21%RH2Q@1%RI2QN1%RJ2R21%RK2R91%RL2R>1%RM2RA1%RN2RF1%RO2RJ1%S02RM1tX>SMS21tVBS=S;1p0SA1p0SJ1pVFT11pW4T11pX6T31pQ:T51")) (only parsing).
Variable L : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow1) 0%nat 0%nat).
Variable pbrk : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow1) 1%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow1) 2%nat 0%nat).
Variable cur : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow1) 3%nat 0%nat).
Lemma KL2_brk_grow1 : ltac:(sec_stmt2 constr:(SEC_T_KL2_brk_grow1) 4%nat 0%nat).
Proof.
intros HK Hph b req.
pose proof alloc_ceiling_lt as Hcl.
pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (Ecur & Ebrk & Epbrk & Ereg).
pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
pose proof (bv_unsigned_in_range 64 b) as Rb. unfold bv_modulus in Rb.
assert (Hcb : cur = bv_unsigned b) by (subst b; lia).
assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
assert (Hne : req <> 0) by (unfold PGSZ in *; lia).
assert (Hb2 : bv_unsigned b + 2 * PGSZ < 2 ^ 64) by (rewrite <- Hcb, Ecur; unfold PGSZ in *; lia).
assert (Hsb : bv_unsigned (vm_start_brk h) <= bv_unsigned b + 2 * PGSZ) by (rewrite <- Hcb, Ecur; unfold PGSZ; lia).
splits; try lia.
- rewrite <- Hcb, Ecur. exact S2.
-
unfold answer_ok, event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
- unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
apply KL2_dead with (pbrk := pbrk). exact HK.
-
intros Hrf Hceil.
assert (Hn : bv_unsigned (Z_to_bv 64 (2 * PGSZ)) = 2 * PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
{ rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
apply (KL2_lbrk_pages_ok L pbrk h cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b1 l1 Hb; rewrite Ereg in Hb; discriminate].
rewrite Hcb, Z_to_bv_bv_unsigned. exact Hrf. }
split.
+ unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
+ unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Z.eqb_refl, Hph.
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
* apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
* rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
* intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
* intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
* intros b0 l0 Hb. rewrite Ereg in Hb. discriminate.
* rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
-- exists (b, Z_to_bv 64 (2 * PGSZ)). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
-- intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
-- intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_KL2_brk_grow2 := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "T@'R7'C'F'Q=r5r4r3%43321'>'QH&R1r6%211(QC%63521'8':%12@@%311&R2r7%211(0(9%14GGCB%3281%B3851'T8yR0%211&Q1%11D&RN%12FM&RB%3221'=r9%62BK%O3Q621&T9r2%22>1%Q33Q:15r1%=23;%Q63Q=21&S1%126>z%Q:3QA21&S0%123:&S4+2+R0%3221%62<1&RO&Q8r8%211%F2Q21%521B&@%QI3R0E@%211'2&QGvQ<r:(R>%11L%54431Q3(<%R33821&QN%1375Q7%R;31Q8B%Q;241&O&1%R22QEQE&Q7%11H&Q4%11J%63531&T7%12QMQG%:33QA1%RC3H1A%QD2R0RF%QM21QK&Q@%11J%Q6231r<%K1RL%O4N21RM%RL3Q11J%I343RO(N%D1Q1(3%RB4R<R<S4@%E1Q4%33I21&Q6%11Q7%QC1Q8%R72RCS:%R@21R>%I2RE1&Q3%11Q=&Q5%11Q?&Q2%11QA%B8A=;:7531%SF3DSC1%RF2F1p0K1p0Q11%RI2Q>1%RJ2QL1%RK2R01%RL2R71%RM2R=1%RN2R@1%RO2RE1%S02RI1%S12RN1tX>T5S31tVDS:S81p0S>1p0SK1p0T31pW<T:1pVBT;1pW4T;1pX6T=1pQ:T?1")) (only parsing).
Variable L : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow2) 0%nat 0%nat).
Variable pbrk : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow2) 1%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow2) 2%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow2) 3%nat 0%nat).
Variable l : ltac:(sec_ty2 constr:(SEC_T_KL2_brk_grow2) 4%nat 0%nat).
Lemma KL2_brk_grow2 : ltac:(sec_stmt2 constr:(SEC_T_KL2_brk_grow2) 5%nat 0%nat).
Proof.
intros HK Hph Ereg br req.
pose proof alloc_ceiling_lt as Hcl.
pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (b' & l' & Ereg' & Ebrk & Epbrk).
rewrite Ereg in Ereg'. injection Ereg' as <- <-.
pose proof (k2_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
pose proof (bv_unsigned_in_range 64 br) as Rb. unfold bv_modulus in Rb.
assert (Hne : req <> 0) by (unfold req, PGSZ in *; lia).
assert (Hal : bv_unsigned br mod PGSZ = 0).
{ subst br. rewrite Ebrk. unfold PGSZ in *. rewrite Z.add_mod, R2, R4 by lia. reflexivity. }
splits; try (subst br req; unfold PGSZ in *; lia).
- unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; unfold req, PGSZ; lia).
unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
- unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; unfold req, PGSZ; lia).
apply KL2_dead with (pbrk := pbrk). exact HK.
- intros Hrf Hceil. subst br. cbv zeta in *.
assert (Hn : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
{ apply (KL2_lbrk_pages_ok L pbrk h (b + l) PGSZ HK); [lia| unfold PGSZ; lia| lia| |].
- rewrite <- Ebrk, Z_to_bv_bv_unsigned. exact Hrf.
- intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
split.
+ unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
+ unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Z.eqb_refl, Hph, Ereg.
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
* apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
* rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
* intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption; try (right; assumption).
unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
* intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
* intros b1 l1 E. injection E as <- <-. splits; auto.
-- clear -R3. unfold PGSZ in *; lia.
-- unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
-- clear -Hceil Ebrk. lia.
-- intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
++ destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
++ exists (vm_brk h, Z_to_bv 64 PGSZ). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
* rewrite Hph. exists b, (l + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; lia.
Qed.
End SE.
Lemma region_free_above : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "O'6':'T8yR0%211%4211%611&RKr1r4%33521&RO&QLr2%211&T9%12=7%6231p081pVH>1'>'2&Or3%23?1;(<%63521p081pX2H1pV@I1pWJH1").
Proof.
induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
specialize (H (e, sz) (or_introl eq_refl)). unfold ehi in H; cbn in H.
replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_KL2_mmap_fixed := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "S:'R7'C'F'Q=r4r3r2%43321'>'QH&R1r5%211(QB%118%73631&RJ%11<'T8yR0%211&T7r1%2241&RB%4261'=r6%D3KG1&S1%1236z%H3O21&S0%1237&RO&RN%12:=&Q@vQ<%211%6241'2&O&Q7r7%211%431Q9I(<%Q93721&J&Q4%117%331Q?O%Q>3<16&RG%12QCQC%QA3?19&QNr9(R?&RC&QF%34QJQ721%6351QKr8(N(3':%12QAQA(9%14QCQCR1QA&M&Q6%11M%Q72R6QC%432R71%:3861&Q8%11Q2&Q1%11Q4&Q3%11Q6&Q5%11Q8&Q2%11Q:%F8Q:Q4;97531%RF3IH1%R02Q11%R12Q51%R22Q;1%R32QD1%R42QL1%R52QO1%R62R41tX2R=R81tV@R>R;1tV>S2RB1p0RE1p0RN1pVFS51pW4S51pX6S71pQ:S91")) (only parsing).
Variable L : ltac:(sec_ty2 constr:(SEC_T_KL2_mmap_fixed) 0%nat 0%nat).
Variable pbrk : ltac:(sec_ty2 constr:(SEC_T_KL2_mmap_fixed) 1%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_KL2_mmap_fixed) 2%nat 0%nat).
Variable cur : ltac:(sec_ty2 constr:(SEC_T_KL2_mmap_fixed) 3%nat 0%nat).
Lemma KL2_mmap_fixed : ltac:(sec_stmt2 constr:(SEC_T_KL2_mmap_fixed) 4%nat 0%nat).
Proof.
intros HK Hph a aw nw.
pose proof alloc_ceiling_lt as Hcl.
pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
assert (Hrf : region_free (vm_reserved h) aw nw = true).
{ apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (k2_resv_top _ _ _ HK). exact He. }
assert (Hmc : map_contains (vm_maps h) aw nw = true).
{ unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
splits.
- exact Ha.
- rewrite Ecur. exact S2.
- lia.
- unfold PGSZ in *; lia.
- exact Hrf.
- exact Hmc.
- unfold mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
- unfold event_post. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota.
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
{ intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
+ intros e [<-|He]; [rewrite elo_pair, ehi_pair, Ua, Un; unfold PGSZ in *; lia|].
destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
pose proof (iv_subtract_sub a1 s1 a (a + PGSZ) e ltac:(lia) ltac:(lia) H1'). lia.
+ intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
+ intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
* unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
* intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
pose proof (Kna _ He) as We.
destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
exists e'. split; [right; eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
+ intros b1 l1 E. injection E as <- <-. splits.
* lia.
* rewrite Ha, Ecur. exact S2.
* lia.
* reflexivity.
* lia.
* intros z Hz. exists e0. split; [exact He0|]. lia.
+ exists a, (2 * PGSZ). splits; [reflexivity| lia| lia].
Qed.
End SE.
Lemma g_remove_split : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "Q@'C'6':%1233%311%415&RK(9r4r3%34::21r2%63921'RL&1&B&4%12AA%34?B19%53C18%72D1'?'='>r6(3r8r7%E4LL21r1%53K21%A3LD1%93L81&QO%128:%E3Q0H6%=3Q021%?251qWBQ21%B2Q31qW@Q41%D2Q51p0F1p0O1pRDQ71pW<Q91pW>Q>1pV>Q?1").
Proof.
intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
destruct (Z.eqb_spec x1 a) as [->|Hne].
- destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
- destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.
Lemma phase_quiet2 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "QF'R7'C'F'Q=r5r3r2%43321&QIr6%211'>'QH&R1%115r7%311%63531'8':%12CC%311&R2%118r8%311%?3531'T8yR0%211&Q8%11K%21G%F3421&Q1%11J%21E%J3821&Q>r:%K11r9%44231Kp061p0;1p0C1p0M1p0Q51p0Q91pW6Q?1pW4Q@1pX6QB1pQ<QD1pQ:QE1").
Proof.
intros L L' pbrk h h' HK Hq E1 E2 E3 E4. pose proof (k2_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv2.
rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.
Section SE.
Local Abbreviation SEC_T_KL2_munmap := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "T9'R7'C'F'Q=r6r5r4%43321&QIr7%211&RK':%12<<(9%14>>:9&R3r8%211%83641'A'>%13E@A&RJ%11C%43HC1%6241&Q?%11H'T8yR0%211&T7%123@r2%3251'=&S0z%221F&S4+2+R0%3221%72K1%9261%C1Mr3%K3Q?21&S1r:&RB%3221%Q03QD1?%A2@4%B2A8&RO&RN%128;&Q@vQ<%211%6241'2&K&Q4r;%211r1%532Q31(<%QB3821&RI%11Q3%QE3;14&QNr=(RA%12LQM%4331Q9r<(N&Q7%11A&L%12BQC&M&Q6%11F%331Q7O&Q8%11I&Q1%11K&Q3%11M&Q5%11O&Q2%11Q1%C8A?;97531%S23FE1&S3&5%RL2R9R9%221D%411%423Q8%611%R8231&I%11J%21Q=%QI221%R>251%R?2>1%R@2Q:1%RA2Q>1%RB2QH1%RC2R01%RD2R21%RE2R41%RF2R:1%RG2R>1tX2RMRI1tV@RNRL1tX0SMS21p0S51p0S=1p0SG1p0SK1pWDT21pW>T31pV>T41pW4T41pX6T61pQ:T81")) (only parsing).
Variable L : ltac:(sec_ty2 constr:(SEC_T_KL2_munmap) 0%nat 0%nat).
Variable pbrk : ltac:(sec_ty2 constr:(SEC_T_KL2_munmap) 1%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_KL2_munmap) 2%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_KL2_munmap) 3%nat 0%nat).
Variable l0 : ltac:(sec_ty2 constr:(SEC_T_KL2_munmap) 4%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_KL2_munmap) 5%nat 0%nat).
Lemma KL2_munmap : ltac:(sec_stmt2 constr:(SEC_T_KL2_munmap) 6%nat 0%nat).
Proof.
intros HK Hq Hin Hlen n aw nw.
pose proof alloc_ceiling_lt as Hcl.
rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
pose proof (k2_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
fold n in A4, A5, A6, B2, B5, B6.
assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
{ destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
destruct Hlen3 as [Hlen1 Hlen2].
assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
assert (Hhas : map_has (vm_maps h) aw nw = true).
{ unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
splits; try assumption; try lia.
- reflexivity.
-
unfold event_post. set (L' := set_groups (g_remove a (ld_groups L)) L).
pose proof (k2_distinct _ _ _ HK) as Kd.
destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
{ intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
{ intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
b + mmap_len l <= a \/ a + n <= b).
{ intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
destruct (pwdisj_In _ _ _ (proj2 (k2_wf _ _ _ HK)) C4 A5) as [E|D].
- exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
- unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
assert (Hlohi : a < a + n) by lia.
assert (Hph' : phase_inv2 (ld_brk L') L' pbrk
(mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
{ eapply phase_quiet2; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]. }
assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
{ intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
assert (Hkeep : forall e, In e (vm_maps h) -> fst e <> aw -> In e (map_remove (vm_maps h) aw)).
{ intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction. }
subst L'. k2_open HK. constructor; try exact Hph'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
+ apply vmwf_remove. exact Kwf.
+ intros e He. destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
pose proof (iv_subtract_sub a1 s1 a (a + n) e ltac:(lia) ltac:(lia) H1'). lia.
+ intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
+ intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
* apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
* intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D. pose proof (Kna _ He) as We.
destruct (iv_subtract_contains (fst e) (snd e) a (a + n) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
+ rewrite Ezz, map_app, <- app_assoc. exact Kd1.
+ intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
* rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
* pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. lia.
-
clear -A5. unfold map_remove. induction (vm_maps h) as [|e es IH]; [destruct A5|]. cbn [List.filter length].
destruct A5 as [->|Hin'].
+ cbn [fst went]. unfold wz. fold aw. rewrite bv_eqb_refl. cbn [negb]. pose proof (List.filter_length_le (fun p : word * word => negb (bv_eqb (fst p) aw)) es). lia.
+ specialize (IH Hin'). destruct (negb (bv_eqb (fst e) aw)); cbn [length]; lia.
- apply RefNodes.live_bytes_map_remove_le.
Qed.
End SE.
Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
- exfalso. apply H1. rewrite E. apply in_map. exact Hy.
- exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.
Lemma map_base_bump : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "G'C'6':%1233%2214%411'>%617&B&4r1%238;1%33<<1qWH91&QJr2%211%94==17%:4>B51%;4?C69%>3=21pWN@1pV>F1").
Proof.
intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_KL2_mprotect := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "SD'R7'C'F'Q=r6r5r4%43321&QIr7%211&RK':%12<<%221=(9%14??;:r3%345A21&R4r8%211%;3841&RO&S2&RN+2%221E&RB%5221&RJ%11J%9231+1%921M%;217%;2K1'T8yR0%211&T7r1%2241%325?'='>&S1%12NCz%43Q@21&S0%123Q2%K2Q3H&Q@vQ<%211%Q1241'2&J&Q6r;%211r2%5321F(<%D3821&Q4%117%:316K%H3<15&RH%11G%K3?18&QNr=(R@&RD%23QLQA1%5341Nr<(N&Q7%11F&M%13GR3Q0&Q8%11J&Q1%11L&Q3%11N&Q5%11Q0&Q2%11Q2%?8=L;97531%RM3BA1%QE2I1%QF2M1%QG2Q21%QH2Q<1%QI2QB1%QJ2QE1tX2R0QL1tV@R1QN1tV>S8R51p0R:1p0RE1p0S21p0S61pW:S=1pW<S>1pVBS?1pW4S?1pX6SA1pQ:SC1")) (only parsing).
Variable L : ltac:(sec_ty2 constr:(SEC_T_KL2_mprotect) 0%nat 0%nat).
Variable pbrk : ltac:(sec_ty2 constr:(SEC_T_KL2_mprotect) 1%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_KL2_mprotect) 2%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_KL2_mprotect) 3%nat 0%nat).
Variable l : ltac:(sec_ty2 constr:(SEC_T_KL2_mprotect) 4%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_KL2_mprotect) 5%nat 0%nat).
Lemma KL2_mprotect : ltac:(sec_stmt2 constr:(SEC_T_KL2_mprotect) 6%nat 0%nat).
Proof.
intros HK Hq Hin Hk2 a aw nw.
pose proof alloc_ceiling_lt as Hcl.
rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
pose proof (k2_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
set (nb := mmap_len l) in *.
assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
assert (Hamod : a mod PGSZ = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
{ destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
assert (Hcm : map_contains (vm_maps h) aw nw = true).
{ unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
splits.
- exact Hamod.
- lia.
- lia.
- exact Hcn.
- exact Hcm.
- reflexivity.
- unfold event_post. cbn [Z.eqb orb]. set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
pose proof (k2_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
b0 + mmap_len l0 <= b \/ b + nb <= b0).
{ intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
destruct (pwdisj_In _ _ _ (proj2 (k2_wf _ _ _ HK)) C4 A5) as [E|D].
- exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
- unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
assert (Hph' : phase_inv2 (ld_brk L') L' pbrk
(mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
{ eapply phase_quiet2; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]. }
subst L'. k2_open HK. constructor; try exact Hph'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
+ intros e He. destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
pose proof (iv_subtract_sub a1 s1 a (a + PGSZ) e ltac:(lia) ltac:(lia) H1'). lia.
+ intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
specialize (Kme b1 l1 k0 Hin1). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
* assert (Eb0 : b0 = b).
{ destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
splits; try assumption; try lia.
intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh). pose proof (Kna _ He) as We.
destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b + q * PGSZ) (b + q * PGSZ + PGSZ) Hlohi ltac:(lia)
ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
ltac:(right; subst a; clear -Hq1; unfold PGSZ in *; nia)) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
* splits; try assumption.
intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh). pose proof (Kna _ He) as We.
assert (D : (b0 + q * PGSZ + PGSZ <= a \/ a + PGSZ <= b0 + q * PGSZ)).
{ destruct (Z.eq_dec b0 b) as [->|Hne].
{ pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia. }
destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh) D) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
+ rewrite map_base_bump. exact Kd.
Qed.
End SE.
Lemma KL2_alloc_top : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "C'R7'C'F'Q=r3r2r1%43321'>&G%115&Q@vQ<%211%63=41p081pW4>1pX6@1pQ:B1").
Proof. intros L pbrk h HK. unfold alloc_top. rewrite (k2_isp _ _ _ HK), stack_max_size_val. lia. Qed.
Lemma KL2_init_sp_window : ltac2:(TCodec.tc2 tcn__CJ_Bridge_KLink "D'R7'C'F'Q=r3r2r1%43321&RO&Q0&T9yR0&Q2%118%4231%7261p091pW4?1pX6A1pQ:C1").
Proof. intros L pbrk h HK. rewrite (k2_isp _ _ _ HK). pose_ceil. unfold sp_window_lo. lia. Qed.
End KL2DEF.
End CEIL_WRAP_1.
