(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib
AsanAcct AsanAcctShape SpinAlg Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanPopFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanPlanSoundSumsK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSumsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSumsK.APSXK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSumsK.APSXK.KnowTests."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSumsK.APSXK.Sound."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPopFree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3SoundK.AX2SK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"]; ["2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3add"; "4le"; "4lt"; "5Forall"; "5firstn"; "5map"; "5nth"; "5repeat"; "5seq"; "6Z"]; ["0E"; "0E'"; "0FS0"; "0FULL"; "0FULL'"; "0K"; "0LIMIT"; "7Z_to_le_bytes"; "7bytes_le_to_Z"; "8Fs"; "9Segment"; ":find_segment"; ":store_ok"; ":word_to_le_bytes"; ";Model"; ";m_fs"]; [";m_vm_lazy"; "<bvmap"; "0M"; "0M'"; "0MR'"; "0R"; "0R'"; "=A_wf"; "=H_off_segments"; "=MInv"; "=lazy_cover"; "=same_but_materialized"; ">NCS"; ">SEALED_W"; ">XIMemcpy"; ">XIMemset"]; [">XIStrncpy"; ">XMemIsZero"; ">XMemcpy"; ">XMemset"; ">XPopFree"; ">a_brk"; ">a_fd"; ">a_ghost"; ">a_maps"; ">a_ss"; ">a_vis"; ">acs"; ">caller_saved"; ">copy_facts"; ">expr_vars_lt"; ">fd_vars_lt"]; [">flat_x"; ">fresh_ok"; ">img_cov"; ">kimg_cut"; ">kn"; ">kn_havoc"; ">kn_vars_lt"; ">kread8e"; ">kreadZ"; ">kread_bytes"; ">kwritable"; ">kwritable_x"; ">kzero_x"; ">maps_vars_lt"; ">mk_ss"; ">nxt"]; [">pairs_vars_lt"; ">pc"; ">popfree_facts"; ">reg"; ">reg_lit"; ">ret_lit"; ">sr_fresh"; ">sr_vars_lt"; ">summary_copy"; ">summary_fill"; ">summary_istrncpy"; ">summary_miz"; ">summary_popfree"; ">with_ss"; ">x_imemcpy"; ">x_imemset"]; [">x_istrncpy"; ">x_memcpy"; ">x_memiszero"; ">x_memset"; ">x_popfree"; ">x_sealed"; "?Mr"; "?allowA"; "?always"; "?cfg_of"; "?cs_ok"; "?hid"; "?node1_stmt"; "?x_stmt"; "Bpiece_ok"; "ASEALED_BYTES"]; ["Cext_call2"; "Acopy_spec"; "Aext_call"; "Afill_spec"; "Aistrncpy_spec"; "Amiz_spec"; "@asanreflect_fx"; "Dpf_bytes"; "Dpopfree_spec"; "EELit"; "EEVar"; "ELHit"; "ESA"; "Eadenot"; "Eedenot"; "Eenv"]; ["Eev"; "Eexpr"; "Ekentry"; "Eknow_lookup"; "Elres"; "Eridx"; "Es_know"; "Es_log"; "Es_regs"; "Esentry"; "Esidecond"; "Esplit_lit"; "Esym_state"; "Etwo64"; "Ezbytes_le_to_Z"; "FelenZ"]; ["Festart"; "Fflat"; "Fknow_ok"; "Fregs_ok"; "Genv_agree"; "Hwbytes"; "Imsteps"; "Jret_ok"; "Kgetr"; "Kmkst"; "Krdn"; "Kseg_rom"; "LTSet"; "Msrealizes"; "Nmem_grows"; "0SEGS"]; ["0SINV"; "OIn"; "ONoDup"; "Padd"; "Pland"; "Ple"; "Plor"; "Plt"; "Pmodulo"; "Pmul"; "Pof_nat"; "Ppow"; "Pto_nat"; "0T"; "0a"; "0allkn"]; ["0argH"; "0args"; "0b"; "0b'"; "0base"; "0bs"; "0c"; "0cmax"; "0cnt"; "0cs"; "0cs0"; "0db"; "0dk"; "0e"; "0entry"; "0f"]; ["0fuel"; "0hs"; "0i"; "0j"; "0k"; "0k'"; "0kc"; "0lb"; "0len"; "0lk"; "0m"; "0model"; "0model'"; "0n"; "0nx"; "0nx0"]; ["0nx2"; "0o"; "0off"; "0r"; "0regs'"; "0ret"; "0rs"; "0s"; "0sb"; "0scfg"; "0seg"; "0segs"; "0sk"; "0sr"; "0sr2"; "0ss'"]; ["QBV"; "QZ_to_bv"; "Qbv"; "Qbv_unsigned"; "0v"; "0vals"; "0w"; "0x"; "0z"; "0zs"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Module APSXK.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.
Section Specs.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Definition fill_spec (entry cmax : Z) : Prop :=
forall mem0 (s c : word) (n : Z) (regs : bvmap 5 word) (ret : word),
0 <= n -> bv_unsigned s + n < 2 ^ 64 ->
store_ok SEGS mem0 s (Z.to_nat n) = true ->
bv_unsigned c < cmax ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
(mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) (seg_rom SEGS))
/\ kept_ok regs regs' /\ getr regs' 10%bv = s.
Definition copy_spec (entry : Z) : Prop :=
forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
0 <= n -> length bs = Z.to_nat n ->
rdn SEGS mem0 src (length bs) = Some bs ->
store_ok SEGS mem0 dst (length bs) = true ->
(bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
(mkst regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
/\ kept_ok regs regs' /\ getr regs' 10%bv = dst.
Definition miz_spec (entry : Z) : Prop :=
forall mem (beg sp : word) (N : Z) (regs : bvmap 5 word) (ret : word),
0 <= N <= 2 ^ 40 -> bv_unsigned beg + N + 8 <= 2 ^ 64 -> 16 <= bv_unsigned sp ->
store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
(bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg) ->
(forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem (seg_rom SEGS))
(mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom SEGS))
/\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 1.
Definition SEALED_BYTES : list byte :=
[Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e]
++ repeat (Z_to_bv 8 0) 4087.
Definition istrncpy_spec (entry src : Z) : Prop :=
forall mem0 (dst : word) (regs : bvmap 5 word) (ret : word),
(forall i, src <= i < src + 9 -> mem0 (Z_to_bv 64 i) = None) ->
store_ok SEGS mem0 dst 4095%nat = true ->
bv_unsigned dst + 4095 < 2 ^ 64 ->
(bv_unsigned dst + 4095 <= src \/ src + 9 <= bv_unsigned dst) ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = dst -> getr regs 11%bv = Z_to_bv 64 src -> getr regs 12%bv = Z_to_bv 64 4095 ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
(mkst regs' ret (wbytes mem0 dst SEALED_BYTES) (seg_rom SEGS))
/\ kept_ok regs regs' /\ getr regs' 10%bv = dst.
End Specs.
Lemma reg_of_ridx : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "C'WBy5%211':'B&TEr2%211r1%53621r3&WA&UJ%117%32=1%;3=51p071p]L>1p^8@1").
Proof.
intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.
Lemma regs_ok_pointwise : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q;'T?'9'TA%211&QAy5'WByR0%211%5241%415&D'Br1(W@z(@%33<21%63851%811&U8r3r2%3221&T>r5&L&TE%116r4(T9%11@%64N431%9281%F3J;1p0@1p^8J1&U3%139A@p031pS<O1p^LQ61pR2Q:1").
Proof.
intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
cbn [edenot]. apply getr_zero.
- apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.
Lemma caller_saved_nodup : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "4'UB':&R<%3221").
Proof.
unfold caller_saved.
repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.
Lemma nth_sr_fresh_out : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "M'9':%211'TA%411&D&UAr1r4%33821%511'B&Lr2&S6r3r5%33219(T9z%211%94B841%:4C972%<3D21p0>1p]6H1p^LF1p]NJ1p\FJ1").
Proof.
intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.
Lemma nth_sr_fresh_in : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q5'9':%211'TA%411'UBr4%2261&Hr2&8r5%22;1%5241'B&Lr3r6(2%44B321&S6%13?4:(T9z%211%:4F641(T:&F%12A<%311%@3K51p0B1p0I1p]8Q01p^LN1p]NQ21p\FQ21").
Proof.
intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
inversion Hnd as [|c' t' Hnotin Hnd']; subst.
cbn [sr_fresh]. destruct j as [|j].
- cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
- cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
else ev E n) (eb E).
Lemma ext_call_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "B'T?':&QAy5'WByR0%211%5241&U4r2r3&T2r1%23341%63541pS>81p]N?1pR2A1").
Proof.
intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.
Lemma ext_call_var : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q7'T?':&QAy5'WByR0%211%5241&Hr1&QL%3221'B&T@&T2r5r4r3%43321&Fr2%2251%9241&U8&WA&UJ&L&R<(2%34L921%511%72L1%92?1%E3K;1p0G1p]8Q21pS>M1p]NQ41pR2Q61").
Proof.
intros E nx R' j Hj. cbn [ext_call ev].
replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
f_equal. f_equal. f_equal. f_equal. lia.
Qed.
Lemma nth_sr_vars_lt' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "N':'9'TA%211'B'5&S7r3r2%3221(?%73621&HuQ0%2261&R>r5&Lr4(T9z%211%54D?41%8271%D3C1>p0;1p0?1p^8K1p^LI1p\6M1").
Proof.
intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
cbn [APK.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.
Lemma regs_after_call : forall E sr R R' nx rv,
regs_ok E sr R -> APK.sr_vars_lt nx sr = true -> kept_ok R R' ->
match rv with Some e => APK.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
regs_ok (ext_call E nx R')
(match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
intros E sr R R' nx rv HR Hsv Hkept Hrv.
pose proof (ext_call_agree E nx R') as Hag.
assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
{ intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
apply regs_ok_pointwise. intros r Hr0.
assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
{ intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
pose proof (ridx_range r) as Hrr.
assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
{ destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
- destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
- rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
exact X. }
destruct rv as [e|]; [|exact GEN].
destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.
Lemma wbytes_same : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QK'9'WBy8%211%411yR0%511'<%115p_@31&UE&UC&WCr1%2291&UJ&8r3%22?1%411%9261&UK+2+R0%3221%?251':&Hr5%=2J1%32A1'B&WAr4%F2M1r2%E11%J231%62Q11%;11(3&Lr6z%<2Q:1%44Q::31%62Q;1%@3Q781p0B1p]8G1p0Q<Q:&U5%13CQ3H%F331Dp051p0N1p[NQB1p]FQ@1p\<QF1").
Proof.
intros bs m a Hnw Hall. apply functional_extensionality. intros x.
pose proof (u64_range x) as Hx.
destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
{ apply wbytes_out; [exact Hnw | lia]. }
destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
2: { apply wbytes_out; [exact Hnw | lia]. }
set (j := Z.to_nat (bv_unsigned x - bv_unsigned a)).
assert (Hxj : x = Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
{ subst j. rewrite Z2Nat.id by lia. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia.
symmetry. apply Z_to_bv_bv_unsigned. }
rewrite Hxj at 1. rewrite wbytes_nth by lia. rewrite Hxj. symmetry. apply Hall. lia.
Qed.
Lemma wbytes_defined : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QD'9'WBy8%211%411yR0%511'<%115p031':&UE&UC&WCr2%22:1&UJ&8r4%22@1%411%9261&UK+2+R0%3221%?251&Hr5%<2J1%32@1&D'B&U5r6&WA%G2OBr3%F11%K231%52Q31%84=G71(1%11Q8%<3Q431%>11p0@1p0E1p]8Q61p[NQ;1p]FQ91p\<Q?1").
Proof. intros bs m a j Hnw Hj. rewrite wbytes_nth by assumption. discriminate. Qed.
Lemma rdn_overlay_all : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R1'9'Q:%211'WByR0%211'<y8%511%311p_@51':&UE&UC&WCr2%22<1&UJr3%211%7241&UK+2+R0%3221%=251'O'Azr1%B221&UGr5%@11%3251%8251'Br7&WA%I2Q37%K21I%32Q51%511(3r4%22Q51%:3Q541p0<1p]6F1%QA1Q9%Q<11&U:r6%24@19E&M%13Q?Q5G%=271%E3741p0:1p0Q21p\6QD1p[NQH1p]LQC1p]FQE1p^HQN1").
Proof.
intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
cbn [rdn repeat].
pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
rewrite (IH (a + 1)%bv b); [reflexivity | rewrite Hu1; lia |].
intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hall. lia.
Qed.
Lemma rdn1_overlay : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q5'9'Q:%211'WByR0%211'<y8%511%311p_@51'Br3r2%211(3r1%2291%73941%C1;%>11&U:r5r4u1%4432=1(6(;%11D%33E@1%?2;1%D3;61p0>1p\6I1p[NM1p]FI1p^HQ21").
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.
Lemma rdn_nth : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R2'9'Q:%211'WByR0%211'<y8%511%311p051':%<14&UE&UC&WCr3%22=1&UJr4%211%7241&UK+2+R0%3221%=251'B%F1@&U:r7r6r5%4432>1(3%12GC%93831&H%12F7r9r8&WA%K2Q6;%M21G%32Q81u1%A47621(6&Lz%92Q;1%34Q;Q0C1(;%11Q=%73Q>31%E2Q;1%M3L:1p0C1p0F1p0Q11p]8QA1p\<QA1p[NQI1p]LQD1p]FQF1p^HQO1").
Proof.
intros segs m n; induction n as [|n IH]; intros a bs j Hnw H Hj; [lia|].
cbn [rdn] in H.
destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:Hb0; [|discriminate].
destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection H as <-.
destruct j as [|j'].
- cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. rewrite Hb0. reflexivity.
- cbn [nth]. destruct n as [|n'']; [lia|].
assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1)%bv + Z.of_nat j') by lia.
apply (IH (a + 1)%bv rest j'); [lia | exact Hrest | lia].
Qed.
Lemma rdn_of_nth : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R7'9'Q:%211'WByR0%211'<y8%511%311p051':p014&UE&UC&WCr2%22=1&UJr3%211%7241&UK+2+R0%3221%=251&Hr1r5%3221'B%Q01H%K11&U:r8r7&WA%G2Q29%E1G%J221%42Q51u1%948721(3(6r4%11O(;%11Q9%53Q:31%72C1%E3C91p0G1p]8Q;1r6%F4D1:K&K&N(2%221O%44QBQEQ:1%B2N1%Q03N71p0:1p0Q71p]0QF1p[NQN1p]LQI1p]FQK1p^HR41").
Proof.
intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
cbn [rdn seq map].
pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
injection H0 as ->.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
apply Hall. lia.
Qed.
Lemma land_shl_disjoint : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "O'O&UEzr3%3221r2%5241'Ar4%8271&UG&UK+2%221:%4261%8261'B&UD&UIr6%928<%3221r5%6221%83H1Fp0:1p0D1p0G1p]:L1p\6M1p[NN1").
Proof.
intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hl|Hh].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shl_disjoint : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q1'O&UEzr3%3221r2%5241'Ar4%8271&UG&UK+2%221:%4261%8261'B&UF&UIr6%928<%3221r5%6221&UC%1243%:3J31p0<1p0F1p0I1p]:N1p\6O1p[NQ01").
Proof.
intros a b k Ha Hk Hb.
rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.
Lemma Z_to_le_bytes_of_bytes : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "?'9'WBy8%211%411'B&Q7&8r1%2261&Q8%113%6231%83915p\<:1").
Proof.
induction bs as [|b rest IH]; [reflexivity|].
cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
pose proof (bytes_le_to_Z_nonneg rest) as Hr.
assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
{ rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
rewrite Hlor. f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
change (2 ^ 8) with 256 in *. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma word_to_le_bytes_of_bytes : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "H'9'WBy8%211%411'G&8r1%2251u8%5221'B&Q=r2%82;1&WAyR0&Q8%115%4231%8261%:3A18p0<1p\<C1").
Proof.
intros bs Hlen. unfold word_to_le_bytes.
pose proof (AX2SK.bytes_le_to_Z_bound bs) as Hb.
assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
{ eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.
Lemma word_to_le_bytes_of_bytes_n : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "M':'9'WBy8%211%411'B&8r1%2251r2%53;21'Gr3u8%3221&Q=r4&WAyR0&Q8%118%4231%7261%B3C1;p0:1p0?1p\<F1p]LL1").
Proof. intros n bs <- Hn. apply word_to_le_bytes_of_bytes. exact Hn. Qed.
Section KnowTests.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma adenot_SA : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "F'T?'TA'O'B'WByR0%211&T=r3(T<r2r1%3221%6251&WA&U0%1284%32<1%?3<51p^6A1p\6C1pR2E1").
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.
Lemma kwritable_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R4'T?'WByR0%211'<y8%511%311p051'9'TB%211'TA'O&U2vW;r7r6r5%544321r8%746153'B'5&RJr4r3%35;:921(?%73621&UEz%2217'A&Q<r:&WA&U0r;(T<%12HG%4231%62Q81&UL%11J%;4N:31%H3G1B%A2@6&UC%128O&UK+2+R0%3221%H251%F281%G2:1p0I1p0M1p0Q61p0Q91p]LQ@1p^6QA1p\6QC1p]:QE1p\0QF1pS6QJ1pR2R31").
Proof.
intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
cbn [kwritable] in H.
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
{ intros A B. split; [|lia].
replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
- destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
- lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.
Lemma kwritable_x_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R>'T?'WByR0%211'<y8%511%311p051'9'TB%211'TA'O&U2vW;r7r6r5%544321r8%746153'B'5&RKr4r3%35;:921(?%73621'A':&UE&UJr1%211&TOr;%221D%7241&Q<&WA&U0r<(T<%12IM%4231%62Q=1r2%94Q2<21%L3K1Fp0<1p]FE1zr:%;2Q6Q5%>221%I241&UC%G25Q2%2241&UK+2+R0%3221%Q1251%Q4291%Q52?1p0Q71p0Q@1p0QC1p]LQK1p^6QK1p\6QM1p]:QO1p\0R01pS6R41pR2R=1").
Proof.
intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
cbn [kwritable_x] in H.
assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
(c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
by (intros [|] [|]; cbn; auto).
apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
pose proof (u64_range (edenot E n)) as Hnr.
assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
(forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
{ intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
apply Hs; lia. }
apply orb_prop in H as [H|H].
- destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
apply CORE; unfold elenZ in *; lia.
- pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.
Lemma kzero_x_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "RA'T?'WByR0%211'<y8%511%311p051'9'TB%211'TA'O&U2vW;r7r6r5%544321r8%746153'B'5&RLr4r3%35;:921(?%73621'A&UEzr1%3221&UG&TOr;%221D%4261%:261&WA&UC&U0r<(T<%12JN%4231r2%7221%92Q@1%>11(3%<2Q@E%22Q@1%Q13Q@41p0@1p]6Q<1r:%>2Q:Q9%A221%N2M1%J24Q5%E231&UK+2+R0%3221%Q5251%Q7281%Q82=1p0Q:1p0QC1p0QF1p]LQN1p^6QN1p\6R01p]:R21p\0R31pS6R71pR2R@1").
Proof.
intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
cbn [kzero_x] in H.
assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
(c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
by (intros [|] [|]; cbn; auto).
apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
pose proof (u64_range (edenot E n)) as Hnr.
assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
(forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
{ intros A B. split; [|unfold elenZ in *; lia]. intros i Hi.
replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
apply Hz. lia. }
apply orb_prop in H as [H|H].
- destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn zn zl Hall Hxl).
apply CORE; unfold elenZ in *; lia.
- pose proof (xinside_sound segs E M allkn b off n zb zk zn Hall H) as [A B].
unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.
Lemma kimg_cut_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "N'T?'WByR0%211'<y8%511%311p051'9'TB%211'O&U2vW;r5r4r3%544321r6&RCr2%23651%:49481p061p]L=1p[N>1p]:@1pS6D1pR2M1").
Proof.
intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
lazymatch goal with |- context [KImg ?l ?h] => rename l into lo; rename h into hi end.
destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
apply Forall_app. split.
- destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
- destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.
Definition piece_ok (E : env) (M : word -> option byte) (b : expr) (off : Z) (w : nat) (v : expr) : Prop :=
exists bs, rdn segs M (Z_to_bv 64 (estart E (SA b off))) w = Some bs /\ length bs = w
/\ word_to_le_bytes w (edenot E v) = bs.
Lemma lookup_piece : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R4'T?'WByR0%211'<y8%511%311p051'9'TB%211'TA'O':'5%711&U2vW;r8r7r6%544321'A'Gu1r4%3221u8%5231%7231'B'TD&TCr5(7(;%11F'TJ%311%78FEDC6531(T;r3%23A41%=3<41&U1r;(T<%12ML&UJ%11M%63531&SNr<r9%36291Q4Q3Q2p051p0=1p0L1p0Q51p]4Q<1p_:QA1p_>Q@1p^6QB1p\6QD1p]:QF1pS6QJ1pR2R31").
Proof.
intros E M k b off w v hs HK Hw HL Hfl.
pose proof (know_lookup_sound segs E M k b off w false [] [] HK ltac:(lia) ltac:(lia)) as X.
rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
exists bs. rewrite <- adenot_SA. split; [exact Hrd|]. split; [exact Hlen|].
unfold extz in Hv. rewrite <- Hv, <- Hlen. apply word_to_le_bytes_of_bytes. lia.
Qed.
Lemma kread8e_piece : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q@'T?'WByR0%211'<y8%511%311p051'9'TB%211'TA'O&U2vW;r6r5r4%544321'B%A19&RGr3%249761(3r2%22?1%83741&U1r8(T<%12?>+8%53421&SNr9u8%3628FE1Dp051p0<1p0F1p_:N1p^6N1p\6Q01p]:Q21pS6Q61pR2Q?1").
Proof.
intros E M k b off v HK H Hfl. unfold kread8e in H.
destruct (know_lookup segs k b off 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
destruct scs; [|discriminate]. injection H as ->.
eapply lookup_piece; [exact HK | lia | exact HL | exact Hfl].
Qed.
Lemma kreadZ1_byte : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R7'T?'WByR0%211'<y8%511%311p051'9'TB%211'TA'O&U2vW;r6r5r4%544321'B%A18&RHr3u1%35:8721(3r2%22?1%93841&U1r8(T<%12@?+1%53421'A%L1O%Q211&U:&WA&U0r9%;2KJ%3221%52Q;1%74O?1F(6%82Q;N(;%11Q<%43Q=31%J2?1%Q13?71&UEz%221Q6&UG+X0%22Q91%H241%I281p0K1p0Q21p0Q=1p_BQD1p^6QE1p\6QG1p]:QI1pS6QM1pR2R61").
Proof.
intros E M k b off z HK H Hfl. unfold kreadZ in H.
destruct (know_lookup segs k b off 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
pose proof (know_lookup_sound segs E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
destruct bs as [|b0 [|]]; try discriminate.
cbn [edenot] in Hv. unfold extz in Hv. rewrite bytes_le_single in Hv.
apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
pose proof (bv_unsigned_in_range _ b0) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite (Z.mod_small (bv_unsigned b0)) in Hv by (unfold two64; lia).
split; [|rewrite <- Hv; lia]. rewrite <- adenot_SA, Hrd. f_equal. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, <- Hv. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Lemma kread_bytes_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "RN'T?'WByR0%211'<y8%511%311p051'9'TB%211':'TA'O%611&U2vW;r7r6r5%544321'B%C18&RIr4r3%35:7821(3r2%22?1%93841&UEz&U0r9(T<%12A<%4231%7261&UCr:%62GF%9221&UJ%11K%6231&UK+2+R0%3221%C251'A%Q<1Q?%QB11&U:&WAr;%F2Q8Q7%I221%42QJ1r8%74Q=E21&Kr1%92QL1q_BQD1%44QEQM1Q?%Q82?1%Q?3?71&8%12QIQC%QB3QL1;'I%Q:2Q9:&UG+X0%22=1%J241q_BR11%73R21QL%M291%N2=1p0Q01p0Q=1p0QF1p0R11p_DR81p^6R:1p\6R<1p]BR>1p]:R@1pS6RD1pR2RM1").
Proof.
intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
- cbn in H. injection H as <-. split; [reflexivity|]. split; [reflexivity | constructor].
- cbn [kread_bytes] in H.
destruct (kreadZ segs k b off 1) as [z|] eqn:Hz; [|discriminate].
destruct (kread_bytes segs len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
injection H as <-.
assert (Hfl : flat E (SA b off) 1) by (unfold flat; lia).
destruct (kreadZ1_byte E M k b off z HK Hz Hfl) as [Hrd Hzr].
destruct (IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (Hrd2 & Hlen & Hall).
split; [| split; [cbn; lia | constructor; assumption]].
change (S len) with (1 + len)%nat. cbn [map].
change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
eapply rdn_app; [exact Hrd|].
replace (Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1)%bv with (Z_to_bv 64 (estart E (SA b (off + 1)))); [exact Hrd2|].
apply bv_eq. unfold nat_to_word, estart. cbn [a_base a_off]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
change (Z.of_nat 1) with 1. rewrite (Z.mod_small 1) by lia.
rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.
Lemma zbytes_of_small : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q0'9'O%211'I'A&UEzr1%3221&UG+X0%2241%8241q_B<1%;3=17'B&TNr2%211&Q8&K'WBy8%211&WA%123Bq_BI1%74J41:%911%>3L;1p0@1p_DM1").
Proof.
intros zs Hall. rewrite <- zbytes_map. rewrite map_map. f_equal.
induction Hall as [|z rest Hz Hrest IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_copy_facts_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "SH'T?'WByR0%211'<y8%511%311p051'9'TB%211'TA':'O&U2vW;r:r9r8%544321'B%B1;&R=r6r5r7r4r3%68=5;:4321(3r2%22E1%<3;41&UEz%2219'G&UL%11>%321E&U0r>(T<r;%221J%5241%=2<1&UCr?r<%821Q1%;231%521K&UK+2+R0%3221%H251r@%C219%K2J1rAr=%E21Q?%H231%B21Q@%Q121:'C%QL1QO'A&8r1%22R31%Q41N%QF3QN21%R817&U:rB&WArC%Q62FB%Q9221%42RA1%74R461:%QG2@=%R13:21rD%Q?217%:2RG1%QD1Q8%>4R;C21%QN2GQM%R83A21rE%R@4R?1R0Q=p031pS8RI1%L2<1%M2H1q\<O1%Q12Q01p0Q31p0Q:1p0Q>1p0QJ1p0R21p0R71p0R;1p0RI1p]>S31p]LS11p\JS21p^JS31p]2S51p\HS71p^BS81p]:S:1pS6S>1pR2SG1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_copy_facts_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_copy_facts_sound) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_copy_facts_sound) 2%nat 0%nat).
Variable sb : ltac:(sec_ty2 constr:(SEC_T_copy_facts_sound) 3%nat 0%nat).
Variable db : ltac:(sec_ty2 constr:(SEC_T_copy_facts_sound) 4%nat 0%nat).
Lemma copy_facts_sound : ltac:(sec_stmt2 constr:(SEC_T_copy_facts_sound) 5%nat 0%nat).
Proof.
intros fuel.
induction fuel as [|f IH]; intros sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi.
- cbn [copy_facts] in H. injection H as <-. assert (n = 0) by lia. subst n.
exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
- cbn [copy_facts] in H.
assert (STEP : forall (w : nat) v kr,
(1 <= w <= 8)%nat -> Z.of_nat w <= n ->
piece_ok E M sb sk w v ->
copy_facts segs f k sb (sk + Z.of_nat w) db (dk + Z.of_nat w) (n - Z.of_nat w) = Some kr ->
kc = KWord (SA db dk) w v :: kr ->
exists bs, length bs = Z.to_nat n
/\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
/\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc).
{ intros w v kr Hw Hwn (bsP & HrdP & HlenP & HvP) Hr ->.
assert (ES : estart E (SA sb (sk + Z.of_nat w)) = estart E (SA sb sk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
assert (ED : estart E (SA db (dk + Z.of_nat w)) = estart E (SA db dk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
destruct (IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))
as (bsR & HlenR & HrdR & HKR).
exists (bsP ++ bsR). split; [rewrite length_app; lia|]. split.
- replace (Z.to_nat n) with (w + Z.to_nat (n - Z.of_nat w))%nat by lia.
apply rdn_app; [rewrite <- HlenP at 1; rewrite HlenP; exact HrdP|].
rewrite ES in HrdR.
replace (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)%bv with (Z_to_bv 64 (estart E (SA sb sk) + Z.of_nat w)); [exact HrdR|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
- intros M' HM'. constructor.
+ cbn [kentry_ok]. split; [lia|]. split; [unfold flat; lia|].
rewrite adenot_SA, HvP.
pose proof (rdn_firstn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as F.
rewrite F. f_equal. rewrite firstn_app, HlenP, Nat.sub_diag. cbn [firstn]. rewrite firstn_all2 by lia. apply app_nil_r.
+ apply HKR. rewrite ED.
pose proof (rdn_skipn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as Sk.
replace (Z.to_nat (n - Z.of_nat w)) with (Z.to_nat n - w)%nat by lia.
replace (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat w)) with (Z_to_bv 64 (estart E (SA db dk)) + nat_to_word w)%bv.
2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
rewrite Sk. f_equal. rewrite skipn_app, HlenP, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
match type of H with (if ?c then _ else _) = _ => destruct c eqn:H8 end.
+ apply andb_prop in H8 as [H8 Hknown]. apply Z.leb_le in H8.
destruct (copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)) as [kr|] eqn:Hr;
[|destruct (kread8e segs k sb sk); [discriminate|]; destruct (kread_bytes segs 8 k sb sk); discriminate].
assert (Hfl8 : flat E (SA sb sk) 8) by (unfold flat; lia).
destruct (kread8e segs k sb sk) as [v|] eqn:Hv.
* injection H as <-. apply (STEP 8%nat v kr); [lia | lia | | exact Hr | reflexivity].
eapply kread8e_piece; [exact HK | exact Hv | exact Hfl8].
* destruct (kread_bytes segs 8 k sb sk) as [zs|] eqn:Hzs; [|discriminate]. injection H as <-.
apply (STEP 8%nat (ELit (zbytes_le_to_Z zs)) kr); [lia | lia | | exact Hr | reflexivity].
destruct (kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia)) as (Hrd & Hlen & Hsmall).
exists (map (fun z => Z_to_bv 8 z) zs). split; [exact Hrd|]. split; [rewrite length_map; exact Hlen|].
cbn [edenot]. rewrite (zbytes_of_small zs Hsmall).
replace 8%nat with (length (map (fun z : Z => Z_to_bv 8 z) zs)) at 1 by (rewrite length_map; exact Hlen).
apply word_to_le_bytes_of_bytes. rewrite length_map. lia.
+ clear H8. destruct (Z.leb 1 n) eqn:H1.
* apply Z.leb_le in H1.
destruct (know_lookup segs k sb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
destruct scs; [|discriminate].
destruct (copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)) as [kr|] eqn:Hr; [|discriminate].
injection H as <-. apply (STEP 1%nat v kr); [lia | lia | | exact Hr | reflexivity].
eapply lookup_piece; [exact HK | lia | exact HL | unfold flat; lia].
* injection H as <-. apply Z.leb_gt in H1. assert (n = 0) by lia. subst n.
exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
Qed.
End SE.
End KnowTests.
Section Sound.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.
Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis SEGS_wr : segs_wr_ok.
#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
#[local] Notation HID := (hid A argH) (only parsing).
#[local] Notation MR := (Mr A argH) (only parsing).
#[local] Ltac aps_fill :=
first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
| exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT].
Lemma w_reg_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QI'T?'R;&QAy5'WByR0%211%5241'<y8%611%311p061'Q>':'SJvU?v0vQ6vU@vV0vQ2r6r5r4r3r2%<;;:987654321'A&H(2%2215uQ0%4271%6231'B&U8&WA&UJ%11>%32Q51%52C1&T>r8&S3r7%221E%5241%=3Q:71p0?1p0G1p]LQ51p]HQ71pR8Q91pS<Q?1p\DQF1pR2QH1").
Proof. intros. eapply reg_sound; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_reg_lit_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R6'T?'R;&QAy5'WByR0%211%5241'<y8%611%311p061'Q>':'O'SJvU?v0vQ6vU@vV0vQ2r7r6r5r4r3%<;;:987654321'A&H(2%2215uQ0%4271%6231'B%M1F&S4r8%221>(3%12K?%73631&U8&WA&UJ%11F%32Q=1%52:1%52Q=H%?3Q=21&UEz%221L&UG&TM%22O1%M241%N281p0A1p0J1p0Q21p_BQ@1p]LQB1p]HQD1pR8QF1pS<QL1p\DR31pR2R51").
Proof. intros. eapply reg_lit_sound; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_split_lit_denot : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q2'T?'TA'O'B'>%1243&TKr3%211(=r2r1%34;:21%:3851'WByR0%211&T>r5r4%3221&WA&UC&WC%726A%22:1%421@%62<1%I3<81p0@1p]:L1p\6N1p\LO1pR2Q11").
Proof. intros. eapply split_lit_denot; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_know_ok_havoc : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R1'T?'WByR0%211'<y8%511%311p051p_@62'9'TB%211'TA'O&U2vU?r7r6r4%544321'E&UG&WCr1%22G1&U0r9(T<r5%221;%5241%:271&UE&UC&TOr3%22:1%4271%621>%C281'Br8r2%211%B12%53Q721p071p_@Q=1&U>%128Q1r:&RE%14Q4Q3HQ2%Q74Q63<1p051p081p0Q51p]LQ=1p^4Q=1p\6Q?1p]:QA1pS8QE1pS6QG1pR2R01").
Proof. intros. eapply know_ok_havoc; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_flat_x_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QL'T?'WByR0%211'<y8%511%311p051'9'TB%211'TA'O&U2vU?r6r5r4%544321'B'5&R@r3r2%348721(?%73621'A&UEz&U0r8(T<%12A@%4231%7261&UC&WC&T>%128A%32Q71%5271&UK+2+R0%3221%B251&UG%12C8%F231%G2?1p0I1p0Q21p]LQ:1p^6Q:1p\6Q<1p]:Q>1pS6QB1pR2QK1").
Proof. intros. eapply flat_x_sound; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_env_agree_le : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "C':'T?&U4r3r2r1%43321'Gr5r4%3221r6%:3139p031p081pR4>1pR2?1p\8A1p\6B1").
Proof. intros b b' E E' [Hv Hb] Hle. split; [|exact Hb]. intros n Hn. apply Hv. lia. Qed.
Lemma w_cs_ok_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QA'T?'R;&QAy5'WByR0%211%5241'<y8%611%311p061'Q>&U4&ROr4%211r6r5%63321'B'5&RAvVO%2216(?%63521'SJvU?v0vQ6vU@vV0vQ2r8r3%9;8765432CBE1r7%;;:9876541EDGp031p0>1p0F1p]HN1pR8Q01pS<Q61p\DQ=1pR4Q?1pR2Q@1").
Proof. intros. eapply cs_ok_agree; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_hid_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q?':'T?'R;'Q>&U4r5r4r3%43321'GvVOr6%3221'B'5&S0r7&4'>'TA%2211&R:%11@&R7%11B%83531%;2:1(?%?3>21'WByR0%211p[N1B&SKv0vV0%3521ION%4532EQ0O%I3621p0;1p0L1p0Q11p]HQ71p\DQ91pR4Q;1pR2Q<1p\6Q>1").
Proof. intros. eapply hid_agree; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_cs_ok_frame : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "RL'T?'R;&QAy5'WByR0%211%5241'<y8%611%311p061'Q>'TL'SJvU?v0vQ6vU@vV0vQ2r9r8r7r6r5%<;;:987654321&QKr2%2251'QI&SGr;r:%33B21r3%6221&U3r<&TH%11A%4331A'B'9'TI%211&TG%11I(;%115%83531&U2r>&SFr=%26Q7Q431FQ0&TF%11Q4%74Q;631'5&SKr@r?r1%46Q@Q=32J1(?%H3721%Q21Q7%@1Q8%K3QK21p041p[NR21&S=%12;Q9%QL;QKQJQIQHQGQF=1Q9QEQDp041p0B1p0K1p0Q51p0Q;1p0QC1p0QG1p]JR61pR:R81pS>R>1p_0R81p]HR:1pR8R<1pS<RB1p\DRI1pR2RK1").
Proof. intros. eapply cs_ok_frame; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_lazy_cover_cs : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q:'T?'R;&QAy5'WByR0%211%5241'<y8%611%311p061'Q>'SJvU?v0vQ6vU@vV0vQ2r5r4r3r2r1%<;;:987654321&QJ&SKr6%25>;196&Q@%118&SG%13B5=%83531p0:1p]HH1pR8J1pS<Q01p\DQ71pR2Q91").
Proof. intros. eapply lazy_cover_cs; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_A_wf_allowA : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK ";'T?'R;&QG&SGv0r2r1%43321%611p\D81pR2:1").
Proof. intros. eapply A_wf_allowA; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_H_off_segments_cs : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "@'T?'R;'Q>&QHvU?&SKv0vV0r3r2r1%6554321%9281p]H;1p\D=1pR2?1").
Proof. intros. eapply H_off_segments_cs; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma w_fresh_ok_parts : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QN'R;'B'5&RAvVOr1%3221(?%73621'A&S7&ROr2%211&TH&R9%114%311%8251%B3A1<&RF&RD%11:%32:1%G3F1A&RM&R8%11?%32?1%L3K1F&S0&4'>'TA%2211&R:%11H&R7%11J%83531%:2K1%Q83Q71Q2&R>&R5%11Q0%32Q01%Q=3Q<1Q7&R?&R6%11Q5%32Q51%QB3QA1Q<'G%12QAQ8%Q=231%Q>291%Q?2?1%Q@2L1%QA2Q21%QB2Q81p0QD1p\DQM1").
Proof. intros. eapply fresh_ok_parts; try eassumption. Unshelve. all: aps_fill. Qed.
Lemma find_segment_In : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "H'9'Q:%211'O'B'<%115&Q;r4r3r2%43321(3r1%22=1%;3941&UAr5%23A81p041p^FC1p]LB1p[NC1p^HE1").
Proof.
intros segs a n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
- injection H as <-. left. reflexivity.
- right. apply IH. exact H.
Qed.
Lemma wview_rd1 : forall M (a : word) b,
wview SEGS M a = Some b ->
(match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b.
Proof.
intros M a b H. unfold wview in H. destruct (M a) as [b0|]; [exact H|].
unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
destruct (seg_writable seg) eqn:Hw; [|discriminate].
rewrite (SEGS_wr seg (find_segment_In _ _ _ _ Hf) Hw).
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite H. reflexivity.
Qed.
Lemma store_ok_rdn : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QG':'WByR0%211'<y8%511%311p051&UE&UC&WCr1%22;1&UJr3%211%7241&UK+2+R0%3221%=251'B'5&Q<vU?r2r4%443>21(?%83721'C'9%11L'A%Q012&U:r5r6%34>2<1(3%128N%D3731&8%12Q7Q1%G3Q>17%<241q\<>1%A2?1p0C1p0M1p[NQA1pS6Q=1p]LQF1").
Proof.
induction n as [|n IH]; intros M a Hnw Hst.
- exists []. split; reflexivity.
- cbn [store_ok] in Hst. destruct (wview SEGS M a) as [b|] eqn:Hv; [|discriminate].
cbn [rdn]. rewrite (wview_rd1 M a b Hv).
destruct n as [|n'].
+ exists [b]. split; reflexivity.
+ assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
destruct (IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst) as (bs & Hrd & Hlen).
rewrite Hrd. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.
Lemma call_core : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "SJ'R;'T?&QAy5'WByR0%211%5241'<y8%611%311p061'Q>&U<'O'9'TA%211'TB%411':'SJvU?v0vQ6vU@vV0vQ2r<r=r:r9r8%<;;:987654321'B'5&RAvVOr>%3221(?%73621&U4&ROr?%211%4318A'U6&U9&T6&WA&S1r@%211%42QB1&SFr;%26Q2O=51M&U;%11Q5%<5;O631r5%<2QJOr4%@5?3215%B3Q;51&U3r6%23HQ51&U2%14Q@B3Q7rD&S=rF&RN%14OQ5Q>Q?%4231r3r2r1%QK;QJQIQHQGQFQE94321&Q9&Q?%115rB%311%QD3531'U=vW9&SIrA%25R5N1L>%54R6418p071p0>1p]JRC1pR:RE1pS>RK1%Q?1K%:5R=91Q?QG%=4R><1QNp041p0Q01p0Q31p0Q71p0QK1p0R11p0R:1pS:S11p^:S71p^2RJ1p]<RL1p^NRO1p^<S31p[LS51p]HS71pR8S91pS<S?1pR4SF1pR2SG1p\DSI1").
Proof.
intros cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' Hk.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (H := HID E cs model).
unfold cfg_of.
apply (srz_msteps_restricted_T SEGS scfg H
(w_H_off_segments_cs E cs model) SEGS_wx (allowA A E cs)
(mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
(w_lazy_cover_cs E cs R FULL model HC)
(w_A_wf_allowA E cs)
(co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC)).
- rewrite restrict_mkst. exact Hms.
- intros model' Hinv' Hsame Hclean.
set (FULL' := munrestrict H FULL MR').
change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
apply (Hk regs' FULL' model').
+ pose proof (w_cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC1.
pose proof (w_hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
eapply (w_cs_ok_frame E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
* rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
* exact HR'.
* reflexivity.
* cbn [s_know mk_ss]. unfold Mr. rewrite HH.
fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
exact HK'.
* intros a Ha. rewrite HH in Ha.
unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
+ apply (same_but_materialized_frame _ _ Hsame).
Qed.
Lemma sr_vars_lt_fresh : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q1'9':%211'TA%411'B'5&S7r1r3%3221(?%73621'G&F&8r5%22@1%4291r2%7221&S6r6r4%33821%B2@1%E3D1?p071p0@1p\6L1p]NM1p^LK1p^>N1").
Proof.
induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [APK.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_call_node_sound := (forall cs cs' E R FULL model T (ret : Z) rv k' regs' MR', CSOK E cs R FULL model ->
after_call nx0 cs ret rv k' = Some cs' ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
kept_ok R regs' ->
match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
know_ok SEGS E MR' k' ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) T) (only parsing).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_call_node_sound) 0%nat 0%nat).
Variable cs' : ltac:(sec_ty2 constr:(SEC_T_call_node_sound) 1%nat 0%nat).
Variable E : ltac:(sec_ty2 constr:(SEC_T_call_node_sound) 2%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_call_node_sound) 3%nat 0%nat).
Variable FULL : ltac:(sec_ty2 constr:(SEC_T_call_node_sound) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_call_node_sound) 5%nat 0%nat).
Variable T : ltac:(sec_ty2 constr:(SEC_T_call_node_sound) 6%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_call_node_sound) 7%nat 0%nat).
Lemma call_node_sound : ltac:(sec_stmt2 constr:(SEC_T_call_node_sound) 8%nat 0%nat).
Proof.
intros rv k' regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
unfold after_call in Hac.
match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
injection Hac as <-.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (E' := ext_call E (nxt cs) regs').
pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms).
- apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
- eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
- intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.
End SE.
Definition ext_call2 (E : env) (nx : nat) (R' : bvmap 5 word) (vals : list word) : env :=
ext_list (ext_call E nx R') (nx + NCS) vals.
Lemma ext_call2_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "F'T?':&QAy5'WByR0%211%5241'9%113&U4r3r4&T0r2r1%344521%73651p_<91pS><1p]NC1pR2E1").
Proof.
intros E nx R' vals. unfold ext_call2.
destruct (ext_call_agree E nx R') as [H1 H2]. destruct (ext_list_agree (ext_call E nx R') (nx + NCS) vals) as [H3 H4].
split; [|rewrite H2; exact H4]. intros n Hn. rewrite H1 by exact Hn. apply H3. lia.
Qed.
Lemma ext_call2_agree16 : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "K'T?':&QAy5'WByR0%211%5241'9%113&U4&Fr3&QL%3221&T2r4r2%33261&T0r1%245941%<3841p_<>1pS>A1p]NH1pR2J1").
Proof. intros. unfold ext_call2. apply ext_list_agree. Qed.
Lemma ext_call2_at : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "Q9'T?':&QAy5'WByR0%211%5241'9%113&Hr1&8r2%2281%5241'B&T@&T0r6r5r4r3%544321&F&QL%2261%321>%;251&L&WAz%22K1%44KD;1%B3L61p0D1p]6Q31p_<L1pS>O1p]NQ61pR2Q81").
Proof. intros. unfold ext_call2. apply ext_list_at. assumption. Qed.
Section SE.
Local Abbreviation SEC_T_call_node_sound2 := (forall cs cs' E R FULL model T (ret : Z) rv k' extra vals regs' MR', CSOK E cs R FULL model ->
after_call2 nx0 cs ret rv k' extra = Some cs' ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
kept_ok R regs' ->
match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
know_ok SEGS (ext_call2 E (nxt cs) regs' vals) MR' k' ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) T) (only parsing).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_call_node_sound2) 0%nat 0%nat).
Variable cs' : ltac:(sec_ty2 constr:(SEC_T_call_node_sound2) 1%nat 0%nat).
Variable E : ltac:(sec_ty2 constr:(SEC_T_call_node_sound2) 2%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_call_node_sound2) 3%nat 0%nat).
Variable FULL : ltac:(sec_ty2 constr:(SEC_T_call_node_sound2) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_call_node_sound2) 5%nat 0%nat).
Variable T : ltac:(sec_ty2 constr:(SEC_T_call_node_sound2) 6%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_call_node_sound2) 7%nat 0%nat).
Lemma call_node_sound2 : ltac:(sec_stmt2 constr:(SEC_T_call_node_sound2) 8%nat 0%nat).
Proof.
intros rv k' extra vals regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
unfold after_call2 in Hac.
match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
injection Hac as <-.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (E' := ext_call2 E (nxt cs) regs' vals).
pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag. fold E' in Hag.
set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)).
assert (Hsf : APK.sr_vars_lt (nxt cs + NCS) sr1 = true).
{ subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ].
unfold caller_saved, NCS. cbn [length]. lia. }
assert (HR2 : regs_ok E' (match rv with Some e => sr_upd sr1 10 e | None => sr1 end) regs').
{ eapply (regs_ok_agree' (nxt cs + NCS)); [apply ext_call2_agree16 | |].
- destruct rv as [e|]; [|exact Hsf]. apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [exact Hrvv | unfold nxt, NCS; lia].
- subst sr1. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I]. }
eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms HR2 HK').
intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.
End SE.
Lemma ret_lit_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QN'T?'R;&QAy5'WByR0%211%5241'<y8%611%311p061'Q>'O'SJvU?v0vQ6vU@vV0vQ2r6r5r4r3r2%<;;:987654321'B%E1?&S5%119(3%12C7%63531'A&U8&WA+1%22Q41%42B1%42Q4@%>3Q421&U7%113&UEz%221F&UG&TM%22I1%@241%A281%B2;1p0D1p0L1p^8Q:1p]HQ<1pR8Q>1pS<QD1p\DQK1pR2QM1").
Proof.
intros E cs R FULL model r HC H. unfold ret_lit in H.
destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
pose proof (w_reg_sound E cs R FULL model 1 HC ltac:(lia)) as R1.
rewrite Hr in R1. cbn [edenot] in R1.
split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.
Lemma split_lit_vars : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "L'TA'O':'B'>%1254&TKr4%211(=r3r2%34<;21%:3851'5&R>r5%2261(?%@3521%52:4%B3713p031p0:1p]FF1p]:H1p\6J1p\LK1").
Proof.
intros e b k m H Hv. unfold split_lit in H.
destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
injection H as <- <-. cbn [APK.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.
Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.
Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.
Lemma k0_sound : forall E M k db dk ne dst k0,
know_ok SEGS E M k ->
(if off_image_x A k db dk ne then Some k
else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) = Some k0 ->
know_ok SEGS E M k0.
Proof.
intros E M k db dk ne dst k0 HK H.
destruct (off_image_x A k db dk ne); [injection H as <-; exact HK|].
destruct dst; try discriminate. destruct ne; try discriminate. injection H as <-.
apply kimg_cut_sound. exact HK.
Qed.
Lemma wbytes_fill_at : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QD'WByR0%211'<y8%511%311p051'O&UE&UC&WCr4%22<1r2%5221&UK+2+R0%3221%;251'Az%>219&UGr3%22<1%6241'B&U5r7r6&Mr5&UL%11G%43O31&WA%K2Q57%M21>%32Q71%<4;:51(3%12Q6:%@3Q631p0B1p0J1p]6Q71p]LQ81p\6Q<1p^@Q@1pS6Q<1").
Proof.
intros M s b n i Hnw Hi.
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite wbytes_nth by (rewrite repeat_length; lia). f_equal. apply nth_repeat_lt. lia.
Qed.
Lemma Z_to_bv8_mod : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK ">'O'B'WBy8%211&WA&UHr1+X0%3221%5271%6284%;3821p\>=1").
Proof.
intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_mod. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_summary_fill_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "I'O&T3vU?r2r1%43321&SLvW9v0vVOvQ6vU@vV0vQ2&SH'R;&S9r4r3%35;:?21q\D51%?:C>=<;:9871p0A1p\@G1p\NH1")) (only parsing).
Variable entry : ltac:(sec_ty2 constr:(SEC_T_summary_fill_sound) 0%nat 0%nat).
Variable cmax : ltac:(sec_ty2 constr:(SEC_T_summary_fill_sound) 1%nat 0%nat).
Lemma summary_fill_sound : ltac:(sec_stmt2 constr:(SEC_T_summary_fill_sound) 2%nat 0%nat).
Proof.
intros SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_fill_eq in Hn. unfold summary_fill_ref in Hn.
destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
destruct (Z.ltb c cmax) eqn:Hcm; [|discriminate]. cbn [negb] in Hn. apply Z.ltb_lt in Hcm.
destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hn0 Hn40].
apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb. unfold two64 in Hb.
destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
pose proof (u64_range nw) as Hnr. fold n in Hnr.
assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.
assert (FIN : forall k',
store_ok SEGS M s (Z.to_nat n) = true ->
know_ok SEGS E (wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))) k' ->
after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) T).
{ intros k' Hst HK' Hac.
destruct (SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
as (regs' & Hms & Hkept & Ha0).
rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- exact HK'.
- exact Hk. }
assert (ST0 : n = 0 -> store_ok SEGS M s (Z.to_nat n) = true) by (intros ->; reflexivity).
assert (WB0 : n = 0 -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M) by (intros ->; reflexivity).
destruct (Z.eqb nhi 0) eqn:Hnhi0.
{ apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
apply (FIN (kn cs)); [exact (ST0 Hz) | rewrite (WB0 Hz); exact HKN | exact Hn]. }
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzb end.
{ apply andb_prop in Hzb as [Hzb Hwr]. apply andb_prop in Hzb as [Hc8 Hkz]. apply Z.eqb_eq in Hc8.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz) as (Zb & _ & _).
rewrite Hse, Hlen in *.
apply (FIN (kn cs)); [apply Wst; lia | | exact Hn].
destruct (Z.eq_dec n 0) as [Hz|Hnz]; [rewrite (WB0 Hz); exact HKN|].
assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
rewrite wbytes_same; [exact HKN | rewrite repeat_length; lia |].
intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
rewrite Hus. rewrite Zb by lia. rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity. }
clear Hzb.
match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
pose proof (k0_sound E M (kn cs) db dk (reg cs 12) (reg cs 10) k0 HKN Hk0) as HK0.
destruct (kwritable_x (kn cs) (kn cs) db dk (reg cs 12)) eqn:Hwr; [|discriminate].
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
rewrite Hse, Hlen in *.
eapply FIN; [apply Wst; lia | | exact Hn].
set (M' := wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))).
assert (HK1 : know_ok SEGS E M' (kn_havoc k0 db dk (reg cs 12))).
{ eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
intros x Hx. rewrite Hlen in Hx. destruct (Z.eq_dec n 0) as [Hz|Hnz]; [subst M'; rewrite (WB0 Hz); reflexivity|].
assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
subst M'. apply wbytes_out; rewrite repeat_length; lia. }
destruct (Z.ltb 0 nlo) eqn:Hpos; [|exact HK1]. apply Z.ltb_lt in Hpos.
assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
assert (FILL : forall i, 0 <= i < n -> M' (Z_to_bv 64 (estart E (SA db dk) + i)) = Some (Z_to_bv 8 c)).
{ intros i Hi. subst M'. rewrite <- Hus. apply wbytes_fill_at; lia. }
constructor; [|exact HK1].
destruct (Z.eqb (c mod 256) 0) eqn:Hc8; cbn [kentry_ok]; rewrite Hlen.
- apply Z.eqb_eq in Hc8. split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity.
- split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite Z_to_bv8_mod. reflexivity.
Qed.
End SE.
Lemma store_ok_sub : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QF'WByR0%211'<y8%511%311p051':&UE&UC&WCr4%22<1&UJr3%211%7241&UK+2+R0%3221%=251'B'5&Q<vU?r6r5%44321A(?%83721%E2O5%H21D%G2Q16%E1G%J221r7%K2Q51%I1<%N221%Q0251r9%B4A1@?%E3D1>p041p0=1p0@1p0J1p]FQ91p\6Q@1p]LQ;1p[NQB1pS6Q>1").
Proof.
intros M a n b m Hnw Hst Hlo Hhi. apply store_ok_of_all; [lia|].
intros x Hx. eapply (store_ok_all SEGS M n a Hnw Hst). lia.
Qed.
Lemma summary_miz_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "E&T5vU?&SBv0%211%5241&SLvW9vVOvQ6vU@vV0vQ2&SH'R;&S;r1%23>91q\D41%=:B<@;:98761p0?1").
Proof.
intros SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_miz_eq in Hn. unfold summary_miz_ref in Hn.
destruct (Z.eqb (pc cs) (x_memiszero A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsb.
destruct (split_lit (eaddz (reg cs 2) (-16))) as [qb qk] eqn:Hsq.
destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hap].
apply andb_prop in Hcond as [Hcond Hwr]. apply andb_prop in Hcond as [Hcond Hsphi'].
apply andb_prop in Hcond as [Hcond Hsplo']. apply andb_prop in Hcond as [Hcond Hb8].
apply andb_prop in Hcond as [Hn0 Hn40].
apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.leb_le in Hb8. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'.
unfold two64 in Hb8, Hsphi'.
destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
pose proof (w_reg_sound E cs R FULL model 2 HC ltac:(lia)) as R2.
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
set (beg := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *.
set (nw := edenot E (reg cs 11)) in *. set (N := bv_unsigned nw) in *.
pose proof (u64_range nw) as Hnr. fold N in Hnr. pose proof (u64_range beg) as Hbr. pose proof (u64_range spw) as Hsr.
assert (HnwN : Z_to_bv 64 N = nw) by (apply Z_to_bv_bv_unsigned).
assert (HlenN : elenZ E (reg cs 11) = N) by reflexivity.
pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
unfold eaddz in Hq. rewrite mkAlu_denot, alu_add in Hq. cbn [edenot] in Hq. fold spw in Hq. unfold v_add in Hq.
destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 16 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
set (Q := estart E (SA qb qk)) in *.
assert (HQ : Q = bv_unsigned spw - 16).
{ apply (f_equal bv_unsigned) in Hq. rewrite !u_lit64 in Hq. unfold two64 in Hq.
change (estart E (SA qb qk)) with Q in Hq.
rewrite (Z.mod_small Q) in Hq by lia.
rewrite <- Hq.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (Hstk : store_ok SEGS M (Z_to_bv 64 (bv_unsigned spw - 8)) 8 = true).
{ apply (store_ok_sub M (Z_to_bv 64 Q) 16); rewrite ?u64_lit by lia; try lia. exact Qst. }
pose proof (w_split_lit_denot E (reg cs 10) bb bk Hsb) as Hbeg. fold beg in Hbeg.
destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) bb bk (reg cs 11) HKN HKN Hkz) as (Zb & Blo & Bhi).
rewrite HlenN in Zb, Bhi.
pose proof (ranges_apart_x_sound SEGS E M (kn cs) qb qk (ELit 16) bb bk (reg cs 11) HKN Hap) as Hapart.
rewrite HlenN in Hapart. change (estart E (SA qb qk)) with Q in Hapart.
replace (elenZ E (ELit 16)) with 16 in Hapart by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
set (B := estart E (SA bb bk)) in *.
assert (HuB : bv_unsigned beg = B \/ (B = 2 ^ 64 /\ bv_unsigned beg = 0)).
{ destruct (Z.eq_dec B (2 ^ 64)) as [HB|HB].
- right. split; [exact HB|]. rewrite Hbeg. change (bv_unsigned (edenot E bb) + bk) with B. rewrite HB. reflexivity.
- left. rewrite Hbeg. apply u64_lit. lia. }
assert (Hdisj : bv_unsigned beg + N <= bv_unsigned spw - 8 \/ bv_unsigned spw <= bv_unsigned beg) by lia.
assert (Hz : forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
rdn SEGS M a 1 = Some [Z_to_bv 8 0]).
{ intros a Ha. apply rdn1_overlay.
destruct HuB as [HuB|[HB Hu0]]; [|lia].
replace a with (Z_to_bv 64 (B + (bv_unsigned a - B))) by (rewrite <- (Z_to_bv_bv_unsigned 64 a) at 2; f_equal; lia).
apply Zb. lia. }
destruct (SUM M beg spw N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hdisj Hz Hrok R1 R2 R10
ltac:(rewrite HnwN; exact R11)) as (regs' & Hms & Hkept & Ha0).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (ELit 1)) _ regs' _ HC Hn).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
replace (elenZ E (ELit 16)) with 16 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
apply wbytes_out; rewrite length_N_to_le_bytes, u64_lit by lia; lia.
- exact Hk.
Qed.
Section SE.
Local Abbreviation SEC_T_summary_copy_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "F'O&T1vU?r1%3221&SLvW9v0vVOvQ6vU@vV0vQ2&SH'R;&S8r3%25?:9>1q\D41%>:A=<;:98761p0@1p\NE1")) (only parsing).
Variable entry : ltac:(sec_ty2 constr:(SEC_T_summary_copy_sound) 0%nat 0%nat).
Lemma summary_copy_sound : ltac:(sec_stmt2 constr:(SEC_T_summary_copy_sound) 1%nat 0%nat).
Proof.
intros SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_copy_eq in Hn. unfold summary_copy_ref in Hn.
destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
remember (reg cs 12) as ne eqn:Hne.
destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr0. pose proof (u64_range sr) as Hsr1.
assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
pose proof (w_split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
pose proof (w_split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
assert (Hsre : Z_to_bv 64 (estart E (SA sb sk)) = sr) by (rewrite Hss; reflexivity).
assert (Hlen : elenZ E ne = n) by reflexivity.
assert (FIN : forall k' bs,
length bs = Z.to_nat n ->
rdn SEGS M sr (length bs) = Some bs ->
store_ok SEGS M s (length bs) = true ->
(bv_unsigned s + n <= bv_unsigned sr \/ bv_unsigned sr + n <= bv_unsigned s) ->
know_ok SEGS E (wbytes M s bs) k' ->
after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) T).
{ intros k' bs Hlbs Hrd Hst Hdisj HK' Hac.
destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- exact HK'.
- exact Hk. }
destruct (Z.eqb nhi 0) eqn:Hnhi0.
{ apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
apply (FIN (kn cs) []); [rewrite Hz; reflexivity | reflexivity | reflexivity | lia | cbn [wbytes]; exact HKN | exact Hn]. }
match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
pose proof (k0_sound E M (kn cs) db dk ne (reg cs 10) k0 HKN Hk0) as HK0.
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hwa; [|discriminate] end.
apply andb_prop in Hwa as [Hwr Hap].
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
rewrite Hlen in *.
set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
rewrite Hse in Wst.
assert (HAVOC : forall bs, length bs = Z.to_nat n -> 0 < n ->
know_ok SEGS E (wbytes M s bs) (kn_havoc k0 db dk ne)).
{ intros bs Hlbs Hpos.
assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
apply wbytes_out; rewrite Hlbs; lia. }
assert (HusD : 0 < n -> 0 <= S -> S + n <= 2 ^ 64 -> bv_unsigned s = D /\ bv_unsigned sr = S).
{ intros Hpos Slo Shi. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }
assert (VARS : fresh_ok nx0 cs = true ->
APK.kn_vars_lt (nxt cs) (kn cs) = true /\ APK.expr_vars_lt (nxt cs) db = true /\ APK.expr_vars_lt (nxt cs) ne = true
/\ APK.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
{ intros Hfresh. destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & _).
split; [exact Fkn|]. split; [| split; [rewrite Hne; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | exact Fsr]].
eapply split_lit_vars; [exact Hspd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
assert (GEN : kwritable_x (kn cs) (kn cs) sb sk ne = true -> flat_x (kn cs) sb sk ne = true ->
forall (W : nat) (u : bool), 8 * Z.of_nat W <= n -> (u = true -> 0 < n) ->
after_call2 nx0 cs ret (Some (reg cs 10))
(map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i))) (seq 0 W)
++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if u then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne)) W
= Some cs' ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) T).
{ intros Hswr Hsfl W u HW Hu Hac.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr) as (SWst & Slo & Shi).
destruct (w_flat_x_sound E M (kn cs) sb sk ne HKN Hsfl) as (_ & _ & Spos).
rewrite Hlen in SWst, Shi. change (bv_unsigned (edenot E ne)) with n in Spos.
change (estart E (SA sb sk)) with S in SWst, Slo, Shi. rewrite Hsre in SWst.
destruct (HusD Spos Slo Shi) as [Hus Husr].
destruct (store_ok_rdn (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia))) as (bs & Hrd & Hlbs).
assert (Hfresh : fresh_ok nx0 cs = true).
{ unfold after_call2 in Hac. destruct (fresh_ok nx0 cs); [reflexivity | cbn [andb] in Hac; discriminate]. }
destruct (VARS Hfresh) as (Fkn & Fdb & Fne & Fsr).
destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
set (vals := map (fun i : nat => Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn (8 * i) bs)))) (seq 0 W)).
eapply (call_node_sound2 cs cs' E R FULL model T ret (Some (reg cs 10)) _ W vals regs' (wbytes M s bs) HC Hac).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- set (E2 := ext_call2 E (nxt cs) regs' vals).
pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag2. fold E2 in Hag2.
assert (Edb : edenot E2 db = edenot E db) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fdb]).
assert (Ene : edenot E2 ne = edenot E ne) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fne]).
assert (ED2 : estart E2 (SA db dk) = D) by (unfold estart; cbn [a_base a_off]; rewrite Edb; reflexivity).
assert (EL2 : elenZ E2 ne = n) by (unfold elenZ; rewrite Ene; reflexivity).
pose proof (rdn_wbytes_hit SEGS bs M s ltac:(rewrite Hlbs; lia)) as Hhit.
apply Forall_app. split.
+
apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (i & <- & Hini). apply in_seq in Hini.
assert (EDi : estart E2 (SA db (dk + 8 * Z.of_nat i)) = D + 8 * Z.of_nat i).
{ unfold estart. cbn [a_base a_off]. rewrite Edb. change (estart E (SA db dk)) with (bv_unsigned (edenot E db) + dk) in *. unfold D. unfold estart. cbn [a_base a_off]. lia. }
cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite EDi; lia|].
rewrite adenot_SA, EDi. cbn [edenot]. unfold E2. rewrite ext_call2_at by (subst vals; rewrite length_map, length_seq; lia).
subst vals. rewrite (nth_map_seq _ W i (Z_to_bv 64 0)) by lia.
assert (Hpiece : length (firstn 8 (skipn (8 * i) bs)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
rewrite (word_to_le_bytes_of_bytes_n 8 _ Hpiece) by lia.
pose proof (rdn_skipn SEGS (wbytes M s bs) (length bs) s bs (8 * i) Hhit ltac:(lia)) as Sk.
pose proof (rdn_firstn SEGS (wbytes M s bs) (length bs - 8 * i) _ _ 8 Sk ltac:(lia)) as Fi.
replace (Z_to_bv 64 (D + 8 * Z.of_nat i)) with (s + nat_to_word (8 * i))%bv; [exact Fi|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, Hus.
rewrite (Z.mod_small (Z.of_nat (8 * i))) by lia. f_equal. lia.
+ apply Forall_app. split.
{
unfold kblob_prefix.
destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
apply find_some in HF as [HinK HKt].
destruct K as [| |[kb ko] [n0| | | | | | |] j| | | | | | |]; try (now constructor).
apply andb_prop in HKt as [HKt Hn0le]. apply andb_prop in HKt as [HKt Hn0pos]. apply andb_prop in HKt as [Hkb Hko].
apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le. subst kb ko.
pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
assert (En0 : elenZ E (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
assert (En0' : elenZ E2 (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
rewrite En0 in HKB. destruct HKB as (Bflat & Blen & Bbytes).
change (estart E (SA sb sk)) with S in Bflat, Bbytes.
destruct Hag2 as [Hag2a Heb2].
assert (HB : kentry_ok SEGS E2 (wbytes M s bs) (KBlob (SA db dk) (ELit n0) j));
[| exact (Forall_cons _ _ _ HB (Forall_nil _)) ].
cbn [kentry_ok]. rewrite En0', ED2, <- Heb2.
refine (conj _ (conj Blen _)).
- unfold flat. rewrite ED2. unfold flat in Bflat. pose proof (Wlo) as Wlo'. pose proof (Whi) as Whi'.
change (estart E (SA db dk)) with D in Wlo', Whi'. lia.
- intros i Hi. rewrite <- Hus.
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (wbytes_nth bs M s (Z.to_nat i)) by (rewrite ?Hlbs; lia).
f_equal.
pose proof (rdn_nth SEGS M (Z.to_nat n) sr bs (Z.to_nat i) ltac:(lia) Hrd ltac:(lia)) as RB1.
rewrite Husr in RB1. specialize (Bbytes (Z.of_nat (Z.to_nat i)) ltac:(lia)).
cbn [rdn] in RB1. rewrite Bbytes in RB1. injection RB1 as RB1. rewrite ?Nat2Z.id in RB1 |- *. symmetry. exact RB1.
}
assert (HKN2 : know_ok SEGS E2 M (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN]).
pose proof (k0_sound E2 M (kn cs) db dk ne (reg cs 10) k0 HKN2 Hk0) as HK02.
assert (HAV2 : know_ok SEGS E2 (wbytes M s bs) (kn_havoc k0 db dk ne)).
{ eapply w_know_ok_havoc; [exact HK02 | | apply wbytes_grows].
intros x Hx. rewrite ED2, EL2 in Hx. apply wbytes_out; rewrite Hlbs; lia. }
destruct u; [|exact HAV2].
constructor; [|exact HAV2].
apply know_ok_unk_intro_pt.
* unfold flat. rewrite ED2, EL2. specialize (Hu eq_refl). lia.
* intros i Hi. rewrite ED2. rewrite EL2 in Hi. rewrite <- Hus.
replace i with (Z.of_nat (Z.to_nat i)) by lia.
apply wbytes_defined; rewrite Hlbs; lia.
- exact Hk. }
assert (HSRC :
(if (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool
then after_call2 nx0 cs ret (Some (reg cs 10))
(map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)))
(seq 0 (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat))
++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne))
(if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat)
else None) = Some cs' ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) T).
{ destruct (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool eqn:Hsw; [|discriminate].
apply andb_prop in Hsw as [Hswr Hsfl].
assert (Hu : Z.ltb 0 nlo = true -> 0 < n) by (intros Hnlo0; apply Z.ltb_lt in Hnlo0; lia).
destruct (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool eqn:HW.
- apply andb_prop in HW as [HW Hp]. apply andb_prop in HW as [HW H256]. apply andb_prop in HW as [Heq Hm8].
apply Z.eqb_eq in Heq. apply Z.eqb_eq in Hm8. apply Z.leb_le in H256. apply Z.ltb_lt in Hp.
apply (GEN Hswr Hsfl); [|exact Hu].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
- apply (GEN Hswr Hsfl); [lia | exact Hu]. }
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzs end.
{ apply andb_prop in Hzs as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz) as (Zb & Slo & Shi).
rewrite Hlen in Zb, Shi. change (estart E (SA sb sk)) with S in Zb, Shi, Slo.
destruct (HusD ltac:(lia) Slo Shi) as [Hus Husr].
apply (FIN (KZero (SA db dk) ne :: kn_havoc k0 db dk ne) (repeat (Z_to_bv 8 0) (Z.to_nat n)));
[apply repeat_length | | | lia | | exact Hn].
- rewrite repeat_length. apply rdn_overlay_all; [lia|]. intros i Hi. rewrite Husr. apply Zb. lia.
- rewrite repeat_length. apply Wst. lia.
- constructor; [| apply HAVOC; [apply repeat_length | lia]].
cbn [kentry_ok]. rewrite Hlen. change (estart E (SA db dk)) with D. split; [unfold flat; lia|].
intros i Hi. rewrite <- Hus. apply wbytes_fill_at; lia. }
clear Hzs.
destruct ne as [z| | | | | | |]; try exact (HSRC Hn).
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc3; [|exact (HSRC Hn)] end.
apply andb_prop in Hc3 as [H2048 Hfl]. apply Z.leb_le in H2048.
destruct (copy_facts SEGS (Z.to_nat nhi) (kn cs) sb sk db dk nhi) as [kc|] eqn:Hcf; [|exact (HSRC Hn)].
assert (Hnn : n = nhi).
{ cbn [xhi] in Hnhi. injection Hnhi as <-. rewrite zlit64_eq. subst n nw. cbn [edenot]. apply u_lit64. }
destruct (w_flat_x_sound E M (kn cs) sb sk (ELit z) HKN Hfl) as (Slo & Shi & Spos).
change (estart E (SA sb sk)) with S in Slo, Shi. change (bv_unsigned (edenot E (ELit z))) with n in Shi, Spos.
destruct (HusD Spos Slo Shi) as [Hus Husr].
destruct (copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))
as (bs & Hlbs & Hrd & HKC).
change (estart E (SA sb sk)) with S in Hrd. change (estart E (SA db dk)) with D in HKC.
rewrite <- Hnn in Hlbs, Hrd, HKC.
apply (FIN (kc ++ kn_havoc k0 db dk (ELit z)) bs); [exact Hlbs | | | lia | | exact Hn].
- rewrite Hlbs, <- Hsre. exact Hrd.
- rewrite Hlbs. apply Wst. lia.
- apply Forall_app. split.
+ apply HKC. rewrite <- Hus, Z_to_bv_bv_unsigned, <- Hlbs. apply rdn_wbytes_hit. rewrite Hlbs. lia.
+ apply HAVOC; [exact Hlbs | lia].
Qed.
End SE.
Lemma img_cov_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "QA'T?'WByR0%211'<y8%511%311p051'9'TB%211'O&U2vU?r5r4r3%544321'B'5&RBr2%23761(?%63521'A&UEr1%22>1&UG%123?%6231r8&WA%12Q1=%311(1%11Q0%D3Q031p081p]6M1p0A1p0I1p\6Q01p[NQ11p]:Q31pS6Q71pR2Q@1").
Proof.
intros E M k a b HK H i Hi. unfold img_cov in H. apply existsb_exists in H as [K [HinK HKb]].
destruct K as [| | |lo hi| | | | | |]; try discriminate.
apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HK1. cbn [kentry_ok] in HK1. destruct HK1 as (_ & _ & HK1).
apply HK1. lia.
Qed.
Lemma SEALED_BYTES_length : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK ":'B':&8'WBy8%211&SO%5221uSoO%93821").
Proof. reflexivity. Qed.
Lemma SEALED_W_bytes : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "A'B'9'WBy8%211%411&Q=u8&WAyR0&QM%3221%6251&J&SO%23;81%@3;41").
Proof.
replace SEALED_W with (bytes_le_to_Z (firstn 8 SEALED_BYTES)) by (vm_compute; reflexivity).
apply word_to_le_bytes_of_bytes_n; reflexivity.
Qed.
Lemma SEALED_BYTES_nth_hi : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "H':'A'Gu8r1%3221&HuSoO%2241%8241'B'WBy8%211&Lr2&SO&WAz%2271%647541%;3812p0=1p]8G1").
Proof.
intros j Hj. unfold SEALED_BYTES. rewrite app_nth2 by (cbn; lia). cbn [length]. apply nth_repeat_lt. lia.
Qed.
Lemma summary_istrncpy_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "G&T4vU?&S@v0%211&SE%113%73631&SLvW9vVOvQ6vU@vV0vQ2&SH'R;&S:r1%23@91q\D41%=:D<B;:98761p0?1").
Proof.
intros SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_istrncpy_eq in Hn. unfold summary_istrncpy_ref in Hn.
destruct (Z.eqb (pc cs) (x_istrncpy A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
destruct (reg_lit cs 11) as [src|] eqn:H11; [|discriminate].
destruct (reg_lit cs 12) as [n|] eqn:H12; [|discriminate].
destruct (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool eqn:Hsn; [|discriminate]. cbn [negb] in Hn.
apply andb_prop in Hsn as [Hsrc Hn95]. apply Z.eqb_eq in Hsrc. apply Z.eqb_eq in Hn95. subst src n.
destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
rename Hcond into Hb. apply Z.ltb_lt in Hb. unfold two64 in Hb.
match goal with Hl : Z.leb 0 (x_sealed A) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hs0 end.
match goal with Hl : Z.ltb (x_sealed A + 9) two64 = true |- _ => apply Z.ltb_lt in Hl; unfold two64 in Hl; rename Hl into Hs9 end.
match goal with Hl : kwritable_x _ _ db dk (ELit 4095) = true |- _ => rename Hl into Hwr end.
match goal with Hl : img_cov k0 _ _ = true |- _ => rename Hl into Hcov end.
match goal with Hl : ranges_apart_x _ db dk (ELit 4095) (ELit 0) _ (ELit 9) = true |- _ => rename Hl into Hap end.
destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
destruct (w_reg_lit_sound E cs R FULL model 11 _ HC ltac:(lia) H11) as [R11 _].
destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
set (s := edenot E (reg cs 10)) in *.
pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
pose proof (k0_sound E M (kn cs) db dk (ELit 4095) (reg cs 10) k0 HKN
ltac:(destruct (off_image_x A (kn cs) db dk (ELit 4095)); [exact Hk0 | destruct (reg cs 10); try discriminate; exact Hk0])) as HK0.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (ELit 4095) HKN HKN Hwr) as (Wst & Wlo & Whi).
pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9) HKN Hap) as Hapart.
rewrite !elenZ_lit in * by lia.
unfold estart in Hapart at 2 3; cbn [a_base a_off edenot] in Hapart. rewrite u_lit0 in Hapart.
set (D := estart E (SA db dk)) in *.
assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
pose proof (img_cov_sound E M k0 _ _ HK0 Hcov) as Hnone.
destruct (SUM M s R (Z_to_bv 64 ret) Hnone ltac:(rewrite <- Hse; apply Wst; lia) ltac:(lia) ltac:(lia)
Hrok R1 R10 R11 R12) as (regs' & Hms & Hkept & Ha0).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) _ regs' _ HC Hn).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- set (M' := wbytes M s SEALED_BYTES).
assert (Hlen : bv_unsigned s + Z.of_nat (length SEALED_BYTES) <= 2 ^ 64) by (rewrite SEALED_BYTES_length; lia).
assert (BY : forall j, (j < 4095)%nat -> M' (Z_to_bv 64 (D + Z.of_nat j)) = Some (nth j SEALED_BYTES (Z_to_bv 8 0))).
{ intros j Hj. subst M'. rewrite <- Hus. apply wbytes_nth; [exact Hlen | rewrite SEALED_BYTES_length; exact Hj]. }
constructor; [|constructor].
+
cbn [kentry_ok]. split; [lia|]. split; [unfold flat; cbn [Z.of_nat]; fold D; lia|].
rewrite adenot_SA. fold D. rewrite <- Hus, Z_to_bv_bv_unsigned.
cbn [edenot]. rewrite SEALED_W_bytes.
replace (firstn 8 SEALED_BYTES) with (map (fun j => nth j SEALED_BYTES (Z_to_bv 8 0)) (seq 0 8)) by reflexivity.
apply rdn_of_nth; [lia|]. intros j Hj. apply rdn1_overlay. rewrite Hus. apply BY. lia.
+
cbn [kentry_ok]. rewrite elenZ_lit by lia.
assert (HD8 : estart E (SA db (dk + 8)) = D + 8) by (unfold D, estart; cbn [a_base a_off]; lia).
rewrite HD8. split; [unfold flat; lia|].
intros i Hi. replace (D + 8 + i) with (D + Z.of_nat (Z.to_nat (8 + i))) by lia.
rewrite BY by lia. f_equal. apply SEALED_BYTES_nth_hi. lia.
+
eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite ?SEALED_BYTES_length; lia.
- exact Hk.
Qed.
Lemma firstn_skipn_map_nth : forall {T} (d : T) k (l : list T) m, (m + k <= length l)%nat ->
firstn k (skipn m l) = map (fun q => nth (m + q)%nat l d) (seq 0 k).
Proof.
intros T d k. induction k as [|k IH]; intros l m Hm; [reflexivity|].
cbn [seq map]. rewrite <- seq_shift, map_map.
destruct (skipn m l) as [|x rest] eqn:Hs.
- exfalso. pose proof (f_equal (@length _) Hs) as HL. rewrite length_skipn in HL. cbn in HL. lia.
- cbn [firstn]. f_equal.
+ rewrite <- nth_skipn, Hs. reflexivity.
+ replace rest with (skipn (S m) l).
2: { replace (S m) with (1 + m)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity. }
rewrite (IH l (S m)) by lia. apply map_ext. intros q. f_equal. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_popfree_facts_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "R>'T?'WByR0%211'<y8%511%311p051'TA'O':'B&WCr1%22=1&U0r9(T<r7r6%3221%6251%;3=81'Gr3&UL%117%4231&UGz%221<&UE&UCr<r:%B21C%E231&UI+4r8%3221%9251&UK+2+R0%3221%?251r=r;%Q021?%Q3231%D2F1&U2vU?r>&U5&T7%Q01G%23Q:C1%43<Q81&S2%16L=KQ=FQ;%:49831p0<1p0B1p0Q31p0Q71p0Q=1p\:R21pR<QK1p^@QM1p\>QN1p\BQO1p]DR01p]@R21pS6R41pR2R=1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 1%nat 0%nat).
Variable lb : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 2%nat 0%nat).
Variable lk : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 3%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 5%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 6%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 7%nat 0%nat).
Variable base : ltac:(sec_ty2 constr:(SEC_T_popfree_facts_sound) 8%nat 0%nat).
Lemma popfree_facts_sound : ltac:(sec_stmt2 constr:(SEC_T_popfree_facts_sound) 9%nat 0%nat).
Proof.
intros Hbase HK Hcnt Hhi Hlo.
unfold popfree_facts. apply Forall_forall. intros Kx Hin.
apply in_map_iff in Hin as [t [<- Hint]]. apply in_seq in Hint.
set (D := estart E (SA lb lk)) in *. set (j := cnt - 1 - Z.of_nat t).
assert (Hj : 0 <= j < cnt) by lia.
cbn [kentry_ok]. split; [lia|].
assert (HDj : estart E (SA lb (lk + 4 * j)) = D + 4 * j) by (unfold D, estart; cbn [a_base a_off]; lia).
split; [unfold flat; rewrite HDj; cbn [Z.of_nat]; lia|].
rewrite adenot_SA, HDj. cbn [edenot].
rewrite word_to_le_bytes4_Z.
replace ((c + Z.of_nat t * s) / 16) with ((c + (Z.of_nat (Z.to_nat cnt) - 1 - j) * s) / 16) by (f_equal; f_equal; lia).
rewrite <- (pf_bytes_cell c s (Z.to_nat cnt) j) by lia.
assert (Hlen : length (pf_bytes c s (Z.to_nat cnt)) = (4 * Z.to_nat cnt)%nat) by apply pf_bytes_length.
rewrite (firstn_skipn_map_nth (Z_to_bv 8 0) 4) by (rewrite Hlen; lia).
assert (Hu : bv_unsigned (Z_to_bv 64 (D + 4 * j)) = D + 4 * j) by (apply u64_lit; lia).
apply rdn_of_nth; [rewrite Hu; lia|]. intros q Hq. apply rdn1_overlay. rewrite Hu.
replace (D + 4 * j + Z.of_nat q) with (bv_unsigned base + Z.of_nat (Z.to_nat (4 * j) + q)) by lia.
apply wbytes_nth; rewrite Hlen; lia.
Qed.
End SE.
Lemma summary_popfree_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "K&T8&T6vU?&SDv0%211%63541'9'TA%211&SLvW9vVOvQ6vU@vV0vQ2&SH'R;&S<r1r2%34B:21q\D51%>:F=D<;:9871p\4@1p0D1").
Proof.
intros SUM args cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
unfold summary_popfree in Hn.
destruct (Z.eqb (pc cs) (x_popfree A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct args as [|[K| | | | | | |] [|]]; try discriminate.
destruct (reg_lit cs 10) as [i|] eqn:H10; [|discriminate].
destruct (reg_lit cs 12) as [c|] eqn:H12; [|discriminate].
destruct (reg_lit cs 21) as [s|] eqn:H21; [|discriminate].
destruct (reg_lit cs 19) as [n|] eqn:H19; [|discriminate].
destruct (split_lit (eaddz (reg cs 11) (- (4 * n)))) as [lb lk] eqn:Hspl.
destruct (xlo (kn cs) (reg cs 11)) as [el|] eqn:Hel; [|discriminate].
destruct (xhi (kn cs) (reg cs 11)) as [eh|] eqn:Heh; [|discriminate].
match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate] end.
repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
apply Z.leb_le in Hcond.
repeat match goal with
| Hl : Z.leb _ _ = true |- _ => apply Z.leb_le in Hl
| Hl : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hl end.
repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
match goal with Hl : fresh_ok nx0 cs = true |- _ => rename Hl into Hfresh end.
match goal with Hl : kwritable_x _ _ lb lk _ = true |- _ => rename Hl into Hwr end.
match type of Hn with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear Hn.
destruct (w_reg_lit_sound E cs R FULL model 10 _ HC ltac:(lia) H10) as [R10 Hi].
destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 Hc].
destruct (w_reg_lit_sound E cs R FULL model 21 _ HC ltac:(lia) H21) as [R21 Hs].
destruct (w_reg_lit_sound E cs R FULL model 19 _ HC ltac:(lia) H19) as [R19 Hnn].
pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hel) as Hel'.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Heh) as Heh'.
repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
set (ew := edenot E (reg cs 11)) in *. set (e := bv_unsigned ew) in *.
pose proof (u64_range ew) as Her. fold e in Her.
set (cnt := n - i) in *.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) lb lk (ELit (4 * cnt)) HKN HKN Hwr) as (Wst & Wlo & Whi).
rewrite elenZ_lit in Wst, Whi by lia.
set (D := estart E (SA lb lk)) in *.
pose proof (w_split_lit_denot E _ lb lk Hspl) as Hsd.
assert (HloD : edenot E (eaddz (reg cs 11) (- (4 * n))) = Z_to_bv 64 (e - 4 * n)).
{ unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64. fold ew. rewrite u_lit64. unfold two64.
rewrite u64_lit by lia. fold e.
replace (e + - (4 * n) mod 2 ^ 64) with ((e - 4 * n) + 1 * 2 ^ 64).
2: { rewrite <- (Z.mod_add (- (4 * n)) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HD : D = e - 4 * n).
{ assert (HDdef : D = bv_unsigned (edenot E lb) + lk) by reflexivity.
rewrite HloD, <- HDdef in Hsd. apply (f_equal bv_unsigned) in Hsd. rewrite !u64_lit in Hsd by lia. lia. }
destruct (SUM R M i e c s n R10 ltac:(unfold e; rewrite Z_to_bv_bv_unsigned; exact R11) R12 R21 R19
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(rewrite <- HD; apply Wst; lia)) as (regs' & Hms & G10 & G12 & G14 & G15 & Gkeep).
set (M' := wbytes M (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) in *.
eapply (call_core cs E E R FULL model T (pc cs + 32) _ _ (nxt cs) regs' M' HC Hfresh (env_agree_refl _ _)).
4: { intros R' FULL' model' HC' Hfs. apply (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' Hfs). }
- rewrite Hpc. exact Hms.
-
apply regs_ok_pointwise. intros r Hr0. rewrite !nth_sr_upd.
pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC r) as HR. unfold sr_get in HR.
assert (Hrz : bv_eqb r 0%bv = false).
{ unfold bv_eqb. apply Z.eqb_neq. intros Hc0. apply Hr0. apply bv_eq. exact Hc0. }
rewrite Hrz in HR.
destruct (Nat.eqb (ridx r) 15) eqn:E15.
{ apply Nat.eqb_eq in E15. rewrite (reg_of_ridx r 15 E15). refine (eq_trans G15 _). rewrite HloD. reflexivity. }
destruct (Nat.eqb (ridx r) 14) eqn:E14.
{ apply Nat.eqb_eq in E14. rewrite (reg_of_ridx r 14 E14). refine (eq_trans G14 _). cbn [edenot]. f_equal; f_equal; lia. }
destruct (Nat.eqb (ridx r) 12) eqn:E12.
{ apply Nat.eqb_eq in E12. rewrite (reg_of_ridx r 12 E12). refine (eq_trans G12 _). cbn [edenot]. f_equal; lia. }
destruct (Nat.eqb (ridx r) 10) eqn:E10.
{ apply Nat.eqb_eq in E10. rewrite (reg_of_ridx r 10 E10). refine (eq_trans G10 _). reflexivity. }
apply Nat.eqb_neq in E15. apply Nat.eqb_neq in E14. apply Nat.eqb_neq in E12. apply Nat.eqb_neq in E10.
rewrite Gkeep; [exact HR| | | |]; intros Hrr; [apply E10 | apply E12 | apply E14 | apply E15]; rewrite Hrr; reflexivity.
-
assert (Hlen : length (pf_bytes c s (Z.to_nat (n - i))) = (4 * Z.to_nat cnt)%nat) by (unfold cnt; apply pf_bytes_length).
assert (Hbase : bv_unsigned (Z_to_bv 64 (e - 4 * n)) = D) by (rewrite HD; apply u64_lit; lia).
unfold know_ok. apply Forall_app_intro; [|apply Forall_app_intro].
+ fold cnt. apply (popfree_facts_sound E M lb lk cnt c s (Z.to_nat K) (Z_to_bv 64 (e - 4 * n)) Hbase); lia.
+ destruct (Z.ltb K cnt) eqn:HKc; [|constructor]. apply Z.ltb_lt in HKc.
constructor; [|constructor]. cbn [kentry_ok]. rewrite elenZ_lit by lia. split; [unfold flat; lia|].
intros q Hq. fold D. replace (D + q) with (bv_unsigned (Z_to_bv 64 (e - 4 * n)) + Z.of_nat (Z.to_nat q)) by lia.
subst M'. apply wbytes_defined; rewrite Hlen; lia.
+ eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite Hlen; lia.
Qed.
Theorem node_x_sound_XIMemset : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "A&T3vU?&S?v0%211+X0%63521&SMvW9vVOvQ6vU@vV0vQ2(QO%89>7<654321p0:1").
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.
Theorem node_x_sound_XMemset : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "A&T3vU?&SCv0%211&TM%63521&SMvW9vVOvQ6vU@vV0vQ2(R3%89>7<654321p0:1").
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.
Theorem node_x_sound_XIMemcpy : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "@&T1vU?&S>v0%211%5241&SMvW9vVOvQ6vU@vV0vQ2(QN%89=7;654321p0:1").
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.
Theorem node_x_sound_XMemcpy : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "@&T1vU?&SAv0%211%5241&SMvW9vVOvQ6vU@vV0vQ2(R2%89=7;654321p0:1").
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.
Theorem node_x_sound_XMemIsZero : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "@&T5vU?&SBv0%211%5241&SMvW9vVOvQ6vU@vV0vQ2(R1%89=7;654321p0:1").
Proof. intros SUM args. exact (summary_miz_sound SUM). Qed.
Theorem node_x_sound_XIStrncpy : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "B&T4vU?&S@v0%211&SE%113%73631&SMvW9vVOvQ6vU@vV0vQ2(R0%89?7=654321p0:1").
Proof. intros SUM args. exact (summary_istrncpy_sound SUM). Qed.
Theorem node_x_sound_XPopFree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundSumsK "A&T8&T6vU?&SDv0%211%63541&SMvW9vVOvQ6vU@vV0vQ2(R4%89=7;654321p0:1").
Proof. intros SUM args. exact (summary_popfree_sound SUM args). Qed.
End Sound.
End APSXK.
