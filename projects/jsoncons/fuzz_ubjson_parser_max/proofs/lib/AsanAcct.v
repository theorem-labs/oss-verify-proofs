(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import CatSim PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanAcct () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct.FPX_1.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"]; ["1true"; "1unit"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3lt"; "4map"; "5N"; "5Z"; "0H"; "0H0"; "0L"; "6Fs"]; ["7Segment"; "7seg_base"; "7seg_size"; "8MachineOk"; "8access_report"; "8access_value"; "8accessed_ranges"; "8code_read_ov"; "8decode_exec_accesses"; "8fetch_failure"; "8fetch_half_any"; "8fetch_half_ov"; "8fetch_tail_any"; "8fetch_word_ov"; "8find_segment"; "8interp_eff_accesses"]; ["8machine_result"; "8machine_state"; "8memory_access"; "8memory_read"; "8mkAccessReport"; "8ms_mem"; "8ms_pc"; "8ms_reg"; "8ms_regs"; "8ms_rom"; "8ms_svc_pending"; "8ov_read_bytes"; "8seg_ov_read_bytes"; "8step"; "8step_accesses"; "8store_ok"]; ["8write_to_mem"; "8wview"; "9SNext"; "9mi_account_step"; "9mkCfg"; "9sstep"; "9step_to"; ":FdEntry"; ":FdState"; ":FsState"; ":InputStream"; ":IoState"; ":LimState"; ":Model"; ":PipeBuf"; ":ProcState"]; [":TimeState"; ":VmMaps"; ":access_pages_acc"; ":accesses_pages"; ":event"; ":m_clock"; ":m_fd"; ":m_fds"; ":m_fs"; ":m_fsys"; ":m_halted"; ":m_io"; ":m_lim"; ":m_pipes"; ":m_proc"; ":m_rlimit_core"]; [":m_stdin"; ":m_tid"; ":m_time"; ":m_vm_lazy"; ":m_vm_materialized"; ":m_vmmaps"; ":materialize_model_accesses"; ":newly_materialized_pages"; ":page_base"; ":page_base_of"; ":page_in_ranges"; ":page_insert"; ":page_mem"; ":page_size"; ":vm_backing_used"; ":vm_limit"]; [":with_vm_backing"; ";bvmap"; "<core"; "<eff"; "0P"; "=A_bytes"; "=A_pages"; "=A_wf"; "=H_off_segments"; "=MInv"; ">node_ok"; "=eager_used"; "=hclean"; "=lazy_cover"; "=mkH"; "=mrestrict"]; ["=munrestrict"; "=page_allowedb"; "=range_avoids"; "=ranges_avoid"; "=ranges_from_b"; "=restrict"; "=same_but_materialized"; "=segs_below_b"; "=unrestrict"; "=woff"; "=wx_segs_nowrap"; "=wx_segs_nowrap_b"; "?msteps"; "@mkst"; "@rdn"; "AIn"]; ["ANoDup"; "Aincl"; "Badd"; "Ble"; "Bmodulo"; "Bmul"; "Bof_N"; "Bof_nat"; "Bpow"; "0X"; "0a"; "0accs"; "0addr"; "0base"; "0bs"; "0c"]; ["0e"; "0f"; "0full"; "0fx"; "0g"; "0k"; "0l"; "0l1"; "0l2"; "0lazy"; "0m"; "0m'"; "0m1"; "0m2"; "0m3"; "0mat"]; ["0mat'"; "0mem"; "0mf'"; "0model"; "0model'"; "0model1"; "0mr'"; "0ms"; "0ms'"; "0ms1"; "0msr'"; "0msr0"; "0n"; "0new"; "0p"; "0pages"]; ["0pc"; "0q"; "0r"; "0ranges"; "0regs"; "0rep"; "0rom"; "0rs"; "0rs'"; "0seg"; "0segs"; "0st"; "CBV"; "Cbv"; "Cbv_add"; "Cbv_unsigned"]; ["0t"; "0top"; "0w"; "0x"; "0z"]]).
Section FPX_1. Context {fx : FPState}.
Definition mrestrict (H : word -> bool) (m : word -> option byte)
: word -> option byte :=
fun a => if H a then None else m a.
Definition munrestrict (H : word -> bool) (full m' : word -> option byte)
: word -> option byte :=
fun a => if H a then full a else m' a.
Definition restrict (H : word -> bool) (ms : machine_state) : machine_state :=
{| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
ms_pc_val := ms_pc_val ms;
ms_svc_pending := ms_svc_pending ms;
ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
ms_mem := mrestrict H (ms_mem ms);
ms_rom := ms_rom ms |}.
Definition unrestrict (H : word -> bool) (full : word -> option byte)
(ms' : machine_state) : machine_state :=
{| ms_regs := ms_regs ms'; ms_fregs := ms_fregs ms';
ms_pc_val := ms_pc_val ms';
ms_svc_pending := ms_svc_pending ms';
ms_resv := ms_resv ms'; ms_fcsr := ms_fcsr ms';
ms_mem := munrestrict H full (ms_mem ms');
ms_rom := ms_rom ms' |}.
Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop :=
forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = None.
Definition wx_segs_nowrap (segs : list Segment) : Prop :=
forall seg, In seg segs ->
seg_executable seg && seg_writable seg = true ->
(Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z.
Definition woff (a : word) (k : nat) : word :=
Z_to_bv 64 (bv_unsigned a + Z.of_nat k).
Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
forall k, (k < n)%nat -> H (woff a k) = false.
Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop :=
forall a n, In (a, n) l -> range_avoids H a n.
Lemma woff_0 : ltac2:(TCodec.tc2 tcn__AsanAcct ":'V=yR0%211'D&T9r1(2%3221%53613pYF71").
Proof.
intros a. unfold woff. apply bv_eq. rewrite Z_to_bv_unsigned.
rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma woff_succ : ltac2:(TCodec.tc2 tcn__AsanAcct "E'V=yR0%211';'D&T9&V>r2(V<+1(B%33:21%63;51r1%9221(3%113%<2:1%>3@41pZ<@1pYFB1").
Proof.
intros a k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma range_avoids_hd : ltac2:(TCodec.tc2 tcn__AsanAcct "F'V=yR0%211'6p021';&T2r3r2(3r1%211%63541'Dr4%118(8%43>21p061p[J>1pYFB1pQJA1").
Proof.
intros H a n Hr. rewrite <- (woff_0 a). apply Hr. lia.
Qed.
Lemma range_avoids_tl : ltac2:(TCodec.tc2 tcn__AsanAcct "I'V=yR0%211'6p021';&T2r3r2(3r1%211%63541r4&V>(V<+1(B%33A21%53B<1%>371<p091p[JA1pYFE1pQJD1").
Proof.
intros H a n Hr k Hk. rewrite woff_succ. apply Hr. lia.
Qed.
Lemma range_avoids_cons : ltac2:(TCodec.tc2 tcn__AsanAcct "N'V=yR0%211'6p]821';'Dr3r2%211(8%53821&T2r4&V>(V<+1(B%33A21%53B<1%8371<r5(3%11@%<33;1p051p0?1p[JF1pYFJ1pQJI1").
Proof.
intros H a n H0 Hr k Hk. destruct k as [|k].
- rewrite woff_0. exact H0.
- rewrite <- woff_succ. apply Hr. lia.
Qed.
Lemma ranges_avoid_nil : ltac2:(TCodec.tc2 tcn__AsanAcct ">'V=yR0%211'6p021&T3r1(<'?';%2281%411%7261pQJ91").
Proof. intros H a n Hin. destruct Hin. Qed.
Lemma ranges_avoid_cons : ltac2:(TCodec.tc2 tcn__AsanAcct "N'V=yR0%211'6p021';':'?%1263%311&T2r4r3r2%43321&T3r5%2214r6(7(>%14C@5:%33>1:%8251p071p0;1pZ>A1p[JF1pYFJ1pQJI1").
Proof.
intros H a n l Ha Hl a' n' [Heq | Hin].
- injection Heq as <- <-. exact Ha.
- exact (Hl a' n' Hin).
Qed.
Lemma ranges_avoid_app : ltac2:(TCodec.tc2 tcn__AsanAcct "I'V=yR0%211'6p021':'?';%2261%411&T3r3r2%3221r4%5213r5&5%13:47%9231p051p081pZB=1pZ@>1pQJD1").
Proof.
intros H l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin | Hin];
[exact (H1 a n Hin) | exact (H2 a n Hin)].
Qed.
Lemma restrict_svc_pending : ltac2:(TCodec.tc2 tcn__AsanAcct "C'V=yR0%211'6p021'QA'D'=%116&QJ&T5r2r1%3221%511%613%:3821p[@<1pQJ>1").
Proof. reflexivity. Qed.
Lemma restrict_pc : ltac2:(TCodec.tc2 tcn__AsanAcct "A'V=yR0%211'6p021'QA'D&QF&T5r2r1%3221%511%613%83<21p[@:1pQJ<1").
Proof. reflexivity. Qed.
Lemma restrict_regs : ltac2:(TCodec.tc2 tcn__AsanAcct "D'V=yR0%211'6p021'QA'D&SAy5%2217&QH&T5r2r1%3221%511%613%;3821p[@=1pQJ?1").
Proof. reflexivity. Qed.
Lemma restrict_reg : ltac2:(TCodec.tc2 tcn__AsanAcct "E'V=yR0%211'6p021'QAy5%711'D&QG&T5r3r2%3221r1%6221%7242%93?21p\6;1p[@>1pQJ@1").
Proof. reflexivity. Qed.
Lemma restrict_rom : ltac2:(TCodec.tc2 tcn__AsanAcct "F'V=yR0%211'6p021'QA'D'=y8%911%311p091&QI&T5r2r1%3221%511%613%=3821p[@?1pQJA1").
Proof. reflexivity. Qed.
Lemma restrict_mem : ltac2:(TCodec.tc2 tcn__AsanAcct "H'V=yR0%211'6p021'QA'D'=y8%911%311p091&QE&T5r2r1%3221%511&SO%714%2261%?3:41p[@A1pQJC1").
Proof. reflexivity. Qed.
Lemma unrestrict_svc_pending : ltac2:(TCodec.tc2 tcn__AsanAcct "I'V=yR0%211'6p021'=y8%711%311p071'QA'D%71:&QJ&T8r3r2r1%43321%611%713%:3921p[@<1pZ6>1pQJD1").
Proof. reflexivity. Qed.
Lemma unrestrict_mem : ltac2:(TCodec.tc2 tcn__AsanAcct "J'V=yR0%211'6p021'=y8%711%311p071'QA'D&QE&T8r3r2r1%43321%611&T0%814%23761%;3=41p[@=1pZ6?1pQJE1").
Proof. reflexivity. Qed.
Lemma restrict_mkst : ltac2:(TCodec.tc2 tcn__AsanAcct "Q2'V=yR0%211'6p021&SAy5%2215'=y8%:11%311p0:1'D'QA&T5r5&T=vU3r4r3r2r1%6554321%9281&SO%12:5%:598715%?3>41p\>A1p[4B1p\2M1p\:I1pQJM1").
Proof. reflexivity. Qed.
Lemma mrestrict_idem : ltac2:(TCodec.tc2 tcn__AsanAcct "C'V=yR0%211'6p021'=y8%711%311p071'D&SOr2r1%3221%4231%63712pZF81pQJ>1").
Proof.
intros H m. apply functional_extensionality. intro a. unfold mrestrict.
destruct (H a); reflexivity.
Qed.
Lemma munrestrict_mrestrict : ltac2:(TCodec.tc2 tcn__AsanAcct "D'V=yR0%211'6p021'=y8%711%311p071'D&T0r2r1&SO%1232%53431%73814pZF91pQJ?1").
Proof.
intros H m. apply functional_extensionality. intro a.
unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.
Lemma mrestrict_munrestrict : ltac2:(TCodec.tc2 tcn__AsanAcct "G'V=yR0%211'6p021'=y8%711%311p071'D&SOr3&T0r2r1%33421%6251%7263%93:21pZF;1pZ6<1pQJB1").
Proof.
intros H full m. apply functional_extensionality. intro a.
unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.
Lemma unrestrict_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "B'V=yR0%211'6p021'QA'D&T8r2&QEr1%211&T5%1253%73631%93:15p[@;1pQJ=1").
Proof.
intros H ms. destruct ms. unfold unrestrict, restrict. cbn.
rewrite munrestrict_mrestrict. reflexivity.
Qed.
Lemma restrict_unrestrict : ltac2:(TCodec.tc2 tcn__AsanAcct "H'V=yR0%211'6p021'=y8%711%311p071'QA'D&T5r3&T8r2r1%33421%6251%7263%93:21p[@;1pZ6=1pQJC1").
Proof.
intros H full ms. destruct ms. unfold unrestrict, restrict. cbn.
rewrite mrestrict_munrestrict. reflexivity.
Qed.
Definition hclean (H : word -> bool) (ms : machine_state) : Prop :=
forall a, H a = true -> ms_mem ms a = None.
Lemma restrict_hclean : ltac2:(TCodec.tc2 tcn__AsanAcct ">'V=yR0%211'6p021'QA&SLr2&T5r1%2231%5241p[@71pQJ91").
Proof.
intros H ms a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
Qed.
Lemma hclean_restrict_id : ltac2:(TCodec.tc2 tcn__AsanAcct "B'V=yR0%211'6p021'QA&SLr2r1%3221'D&T5r3%2216%43917p061p[@;1pQJ=1").
Proof.
intros H ms Hc. destruct ms. unfold restrict. cbn. f_equal.
apply functional_extensionality. intro a. unfold mrestrict.
destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.
Lemma restrict_unrestrict_clean : ltac2:(TCodec.tc2 tcn__AsanAcct "K'V=yR0%211'6p021'=y8%711%311p071'QA&SLr3r1%3221'D&T5r4&T8r2%23381%5241%73<13p091p[@>1pZ6@1pQJF1").
Proof.
intros H full ms Hc. rewrite restrict_unrestrict. apply hclean_restrict_id. exact Hc.
Qed.
Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.
Lemma memory_read1_hidden : ltac2:(TCodec.tc2 tcn__AsanAcct "J'V=yR0%211'D'6vLr1%211(@%63521'=':y8%=11%311%511&QCvV:r2y1%43321(1%118%D3831p0?1pYFG1").
Proof.
intros a Ha. unfold memory_read. cbn [Z.of_N]. rewrite (HH a Ha). reflexivity.
Qed.
Lemma ov_read_bytes_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "Q7';'V=yR0%211'=y8%511%311p051':%114'D%812&QKvV:&SOvLr3%3221r2r4%847321(4r1%22>1%>3=41'Cr5%?4>8;1%72C:%C3B21&T2%13@?5%7231p091pYNI1pYFQ11pZFM1p[JQ61").
Proof.
induction n as [|n IH]; intros m a bs Hr.
- cbn in Hr |- *. split; [exact Hr | intros k Hk; lia].
- cbn [ov_read_bytes] in Hr |- *.
unfold mrestrict in Hr at 1.
destruct (H a) eqn:Ha.
+ rewrite (memory_read1_hidden a Ha) in Hr. discriminate.
+ destruct (match m a with
| Some b => Some b
| None => match memory_read segs a 1 with
| Some (b :: _) => Some b | _ => None end
end) as [b|]; [|discriminate].
destruct (ov_read_bytes segs (mrestrict H m) (a + 1) n) as [rest|] eqn:Hrest;
[|discriminate].
destruct (IH m (a + 1) rest Hrest) as [Hfull Hav].
rewrite Hfull. split; [exact Hr|].
apply range_avoids_cons; assumption.
Qed.
Lemma wview_restrict : forall m a,
wview segs (mrestrict H m) a =
if H a then None else wview segs m a.
Proof.
intros m a. unfold wview, mrestrict. destruct (H a) eqn:Ha; [|reflexivity].
rewrite (HH a Ha). reflexivity.
Qed.
Lemma store_ok_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "Q1';'V=yR0%211'=y8%511%311p051'D'6&QOvV:&SOvLr2%3221r1r3%847321(@%<3;21'Cr4%=4<691%@3?15&T2%13=<4%6231p081pYFK1pZFG1p[JQ01").
Proof.
induction n as [|n IH]; intros m a Hs.
- split; [reflexivity | intros k Hk; lia].
- cbn [store_ok] in Hs |- *. rewrite wview_restrict in Hs.
destruct (H a) eqn:Ha; [discriminate|].
destruct (wview segs m a) as [b|]; [|discriminate].
destruct (IH m (a + 1) Hs) as [Hfull Hav].
split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.
Lemma write_to_mem_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "O':'V=y8%211%411yR0%511'=%115p031&T2vLr1&9r3%22<1%63541'D&R0&SO%1296r2r4%53321%63:32%62>1%93A31p0;1pYFF1pZFD1pYNJ1").
Proof.
induction bs as [|b bs IH]; intros m a Hav; [reflexivity|].
cbn [write_to_mem length] in *.
pose proof (range_avoids_hd H a _ Hav) as Ha.
pose proof (range_avoids_tl H a _ Hav) as Htl.
rewrite <- (IH _ (a + 1) Htl). f_equal.
apply functional_extensionality. intro x. unfold mrestrict.
destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
rewrite Ha. reflexivity.
Qed.
Lemma write_to_mem_hidden : ltac2:(TCodec.tc2 tcn__AsanAcct "Q3':'V=y8%211%411yR0%511'=%115p031&T2vLr2&9r4%22<1%63541'D'6%817(@%43321&R0r5r6r3%443<21%412%;3D21p081p0>1p]8I1pYFJ1pZFH1pYNN1").
Proof.
induction bs as [|b bs IH]; intros m a x Hav Hx; [reflexivity|].
cbn [write_to_mem length] in *.
pose proof (range_avoids_hd H a _ Hav) as Ha.
pose proof (range_avoids_tl H a _ Hav) as Htl.
rewrite (IH _ (a + 1) x Htl Hx). cbv beta.
destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
rewrite Ha in Hx. discriminate.
Qed.
Lemma mrestrict_visible : ltac2:(TCodec.tc2 tcn__AsanAcct "J'V=yR0%211'6p021'=y8%711%311p071'Dr3r1%211(8%53<21&SOr4r2%33281%912%;3=21p071pYFE1pZF?1pQLE1").
Proof. intros H0 m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.
Lemma ov_read_bytes_mrestrict_eq : ltac2:(TCodec.tc2 tcn__AsanAcct "Q2'V=yR0%211'6p021';'=y8%811%311p081&T2r4r1r3%43321'D':%11:%=11&QKvV:&SOr5%221:r2%64521>%746=2?%<3921p0>1pYFL1pZFE1p[JK1pQLM1").
Proof.
intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
cbn [ov_read_bytes]. unfold mrestrict at 1. rewrite (range_avoids_hd H0 a n Hav).
rewrite (IH m (a + 1) (range_avoids_tl H0 a n Hav)). reflexivity.
Qed.
Lemma rdn_mrestrict_eq : ltac2:(TCodec.tc2 tcn__AsanAcct "Q2'V=yR0%211'6p021';'=y8%811%311p081&T2r4r1r3%43321'D':%11:%=11&T>vV:&SOr5%221:r2%64521>%746=2?%<3921p0>1pYFL1pZFE1p[JK1pQLM1").
Proof.
intros H0 n m a Hav. rewrite <- !ov_rdn. apply ov_read_bytes_mrestrict_eq. exact Hav.
Qed.
Lemma wview_mrestrict_eq : ltac2:(TCodec.tc2 tcn__AsanAcct "M'V=yR0%211'6p021'=y8%711%311p071'Dr3r1%211(8%53<21&R1vV:&SOr4%2219r2%63521%736<2%>3@21p0:1pYFH1pZFB1pQLH1").
Proof. intros H0 m a Ha. unfold wview, mrestrict. rewrite Ha. reflexivity. Qed.
Lemma store_ok_mrestrict_eq : ltac2:(TCodec.tc2 tcn__AsanAcct "O'V=yR0%211'6p021';'=y8%811%311p081&T2r4r1r3%43321'D&QOvV:&SOr5%2217r2%64521;%746:2<%93F21p0;1pYFI1pZFB1p[JH1pQLJ1").
Proof.
intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
cbn [store_ok]. rewrite (wview_mrestrict_eq H0 m a (range_avoids_hd H0 a n Hav)).
destruct (wview segs m a); [|reflexivity].
exact (IH m (a + 1) (range_avoids_tl H0 a n Hav)).
Qed.
Lemma find_segment_some_spec : ltac2:(TCodec.tc2 tcn__AsanAcct "Q8':'Q0%211'K'D'=%115&Q>r4r3r2%43321(4r1%22=1%;3941'C&T?r5%23B91&TC&TF&Q1%11=%311%521A&TB%12CB&Q2%11C%911%5271%<251%A281%B2?1p0D1p\DQ31p[JQ21pYJQ31pZ>Q51").
Proof.
induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
cbn [find_segment] in Hf.
destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
- injection Hf as ->. apply andb_true_iff in E as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2.
split; [left; reflexivity | split; assumption].
- destruct (IH addr n seg Hf) as (Hin & H1 & H2).
split; [right; exact Hin | split; assumption].
Qed.
Lemma find_segment_none_spec : ltac2:(TCodec.tc2 tcn__AsanAcct "Q:':'Q0%211'K'D'=%115&Q>r3r2r1%43321(1%11<%:3831&T?r5%23@71&F'C&TC&TF&Q1%11>%311%5219&TBr4%22<1&Q2%11E%:11%6281%=251%?291%A11p0C1p\DQ41p0H1p[JQ41pYJQ51pZ>Q71").
Proof.
induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
cbn [find_segment] in Hf.
destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
[discriminate|].
destruct Hin as [<- | Hin].
- intros [H1 H2]. apply andb_false_iff in E as [E | E].
+ apply Z.leb_gt in E. lia.
+ apply Z.leb_gt in E. lia.
- exact (IH addr n Hf seg Hin).
Qed.
Lemma in_segment_not_hidden : ltac2:(TCodec.tc2 tcn__AsanAcct "Q:'V=yR0%211'Q0&T?r1vV:%33421&TC&TF&Q1r2%211%411&V?r3%22?1%9241&TBr4%62C1+1%4221%=18%?11&Q2%11;%B11%:241%E271'D'6vLr5%211(8%63521p081p0E1p0Q01p\DQ51p]8Q71").
Proof.
intros x seg Hin H1 H2. destruct (H x) eqn:Hx; [|reflexivity].
exfalso. exact (find_segment_none_spec segs (bv_unsigned x) 1 (HH x Hx) seg Hin (conj H1 H2)).
Qed.
Lemma seg_ov_read_bytes_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "R5';'V=yR0%211'=y8%511%311p051'Q0&T?r2vV:%33421&TC&TF&Q1r3%211%411&V?%12C:%8231&TB%42F7&TGr6%211%5241r4%>11%@11&Q2%114%C11%<241%F281r5%F11%H11%813%J11%C231&TH+2+R0%3221%Q1251'D':%11Q<%Q?11&QL&SOvLr7%3221r8%642Q0E1%744Q1F2%<3921p0>1p0J1p0Q91p0QC1pYFQN1p\DQI1pZFQK1p[JR41").
Proof.
induction n as [|n IH]; intros m seg a Hin Hlo Hhi Htop; [reflexivity|].
cbn [seg_ov_read_bytes].
assert (Ha : H a = false) by (apply (in_segment_not_hidden a seg Hin); lia).
unfold mrestrict at 1. rewrite Ha.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z).
{ rewrite bv_add_unsigned.
assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
pose proof (bv_unsigned_in_range 64 a). lia. }
rewrite (IH m seg (a + 1) Hin) by lia. reflexivity.
Qed.
Lemma code_read_ov_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "K'V=yR0%211'=y8%511%311p051'J'D':%116%911&Q7vV:&SOvLr3%3221r2r1%847321%948532%>3;21p[J@1pYFG1pZFC1").
Proof.
intros m a n. unfold code_read_ov.
destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf; [|reflexivity].
destruct (seg_executable seg && seg_writable seg) eqn:Ewx; [|reflexivity].
destruct (find_segment_some_spec segs _ _ seg Hf) as (Hin & H1 & H2).
apply seg_ov_read_bytes_restrict; [exact Hin | exact H1 | | exact (Hwx seg Hin Ewx)].
rewrite N_nat_Z. exact H2.
Qed.
Lemma fetch_word_ov_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "H'V=yR0%211'=y8%511%311p051'DyQ0%:11%811&Q=vV:&SOvLr2%3221r1%73621%83742%=3:21pYFD1pZF@1").
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.
Lemma fetch_half_ov_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "H'V=yR0%211'=y8%511%311p051'Dy@%:11%811&Q;vV:&SOvLr2%3221r1%73621%83742%=3:21pYFD1pZF@1").
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.
Lemma fetch_half_any_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "H'V=yR0%211'=y8%511%311p051'Dy@%:11%811&Q:vV:&SOvLr2%3221r1%73621%83742%=3:21pYFD1pZF@1").
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.
Lemma fetch_tail_any_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "H'V=yR0%211'=y8%511%311p051'DyQ0%:11%811&Q<vV:&SOvLr2%3221r1%73621%83742%=3:21pYFD1pZF@1").
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.
Lemma fetch_failure_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "H'V=yR0%211'=y8%511%311p051'D'Q@'QA%211&Q9vV:&SOvLr2%3221r1%73621%83742%=3:21pYFD1pZF@1").
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.
Lemma interp_eff_accesses_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "R8'SC'V=yR0%211'=y8%511%311p051'SB':&QB%211'D'Q@'Q4'?%1289%311%511&Q?vV:r5&SOvLr4%3221%73651(Q3(QD(>r3r2%34HI21r1%63B21%82B1%H3B:1'E'Cr7r6%F3E21%=4Q2Q3E9%?3K1=%A2K1%Q13K41%H2G=%Q33Q8G1'6%J1@(@%Q73321%F1Er8%11G%Q;3QA31p051p]8QG1&T3%12Q4M%F231%G2>1%H2A1q[6QH1%K2QI1p0M1p\@QG1p[>QL1pZ0QL1pZFQN1p]2R71").
Proof.
induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
try discriminate.
-
injection Hi as <- <- <-. exists m.
split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
apply ranges_avoid_nil.
-
destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
[|discriminate].
destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
rewrite Hfull.
destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
rewrite Hint. cbn [access_value accessed_ranges].
exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
apply ranges_avoid_cons; assumption.
-
destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
by apply length_Z_to_le_bytes.
rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
in Hi by (rewrite Hlen; exact Hav).
destruct (interp_eff_accesses segs k
(mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
rewrite Hint. cbn [access_value accessed_ranges].
exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
+ intros x Hx. rewrite (Hhid x Hx).
apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
+ apply ranges_avoid_cons; assumption.
Qed.
Lemma decode_exec_accesses_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "Q@'QA'V=yQ0%211':&QB%211'D'Q@'Q4%11:%311&Q8vV:&T5vLr4%3221r3%73621(Q3(QDr2r1%33H21%52?1%C3?71'Cr5%A3@1=&T8&QE%114%33B1?%=3Q21<%?2I1%M3I71&T3%12G@&SL%12IF%>231%?261p0A1p\BQ61p[FQ=1p]6Q;1p[@Q?1").
Proof.
intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
destruct (is_ecall w) eqn:Hec.
- injection Hd as <- <-.
split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
rewrite munrestrict_mrestrict. destruct ms; reflexivity.
- destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
destruct (interp_eff_accesses segs
(exec (Z_to_bv 64 isz) i
{| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
c_resv := ms_resv ms |})
(mrestrict H (ms_mem ms)))
as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
as (mf' & Hfull & -> & Hhid & Hrs).
rewrite Hfull. cbn [access_value accessed_ranges].
split; [|split; [exact Hrs|]].
+ unfold unrestrict. cbn.
replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
+ intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.
Theorem step_accesses_restrict : ltac2:(TCodec.tc2 tcn__AsanAcct "Q;'QA':&QB%211'D'Q@'Q4%117%311&QNvV:&T5vLr3%3221%6251(Q3(QDr2r1%33D21%52>1%B3>71'Cr4%@2?1&T8&QE%114%33A1@%=3N1<%?2H1%L3H71&T3%12F@&SL%12HG%>231%?261p0A1p\BQ51p[FQ91p[@Q:1").
Proof.
intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
destruct (fetch_word segs (ms_pc ms)) as [w|].
{ exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
{ exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
{ exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
exfalso. unfold fetch_failure in Hs.
destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
|| match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
| Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
| None => false end); discriminate.
Qed.
Theorem step_restrict_sound : ltac2:(TCodec.tc2 tcn__AsanAcct "QB'QA'D'Q@%113&QMvV:&T5vLr2%3221%6251(Q3r1%22=1%=3;41'E'Q4%11A'C%A12&QNr4%22A1%<26;%G3521&Q5%12J>&T8&QE%118r3%43H21%O3Q061&T3&Q6%12Q3G%32M1&SL%12O8%Q12Q08%Q73Q81:%G231%H261%I2;1%J2D1q\<L1%O2M1p0Q11p[FQ@1p[@QA1").
Proof.
intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
injection Hs as ->.
destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
apply restrict_unrestrict_clean. exact Hcl.
Qed.
Corollary step_restrict_step : ltac2:(TCodec.tc2 tcn__AsanAcct "J'QA'D'Q@%113&QMvV:&T5vLr2%3221%6251(Q3r1%22=1%=3;41r3%<2;1&T8&QE%114%33=1<%:2E1%E3C61p091p[FH1p[@I1").
Proof.
intros ms msr' Hs.
destruct (step_restrict_sound ms msr' Hs) as (rep & Hsa & Hv & _).
unfold RiscvSemantics.step, drop_access_report. rewrite Hsa, Hv. reflexivity.
Qed.
Lemma step_accesses_ecall_shape : ltac2:(TCodec.tc2 tcn__AsanAcct "R7'QA':&QB%211'D'Q@'Q4%117%311&QNvV:r3%3221(Q3(QDr2r1%33A21%52;1%?3;71&F'='V=yR0%211%411&QJ%11@(1%115%J3531%;11'C(<%11Q0%O3Q0H1y8%?11%A11p0?1&QEr4%211r5%411%Q93631&SAy5%221H&QH%119%218%Q@3421%K1<(4&QG(V<+A(B%33<21%52A1%72Q51%QJ3Q591%O2;1%Q02C1%Q12N1p0Q31p0Q@1p\BR11p[FR51p[@R61").
Proof.
intros ms msr' rs' Hs Hsvc.
assert (Hdec : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ msr' rs') ->
rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
/\ ms_svc_pending msr' = Some (ms_reg ms 17)).
{ intros w Hd. unfold decode_exec_accesses in Hd.
destruct (is_ecall w).
- injection Hd as <- <-. cbn. repeat split; reflexivity.
- destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
destruct (interp_eff_accesses segs _ _) as [[[c1 m1] rs1]| |]; try discriminate.
cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn in Hsvc.
exfalso. apply Hsvc. reflexivity. }
unfold step_accesses in Hs.
destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Hf; try discriminate.
unfold fetch_failure in Hf.
destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
|| match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
| Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
| None => false end); discriminate.
Qed.
End ISA.
Definition page_allowedb (A : list (Z * Z)) (p : word) : bool :=
existsb (fun iv => (fst iv <=? bv_unsigned p)%Z
&& (bv_unsigned p + page_size <=? snd iv)%Z) A.
Definition A_wf (A : list (Z * Z)) : Prop :=
Forall (fun iv => (fst iv <= snd iv)%Z /\ (fst iv) mod page_size = 0
/\ (snd iv) mod page_size = 0)%Z A.
Fixpoint A_bytes (A : list (Z * Z)) : Z :=
match A with
| [] => 0
| iv :: r => (snd iv - fst iv) + A_bytes r
end%Z.
Definition lazy_cover (H : word -> bool) (lazy : list (word * word))
(A : list (Z * Z)) : Prop :=
forall w : word,
page_in_ranges (page_base w) lazy = true -> H w = false ->
page_allowedb A (page_base w) = true.
Definition eager_used (m : Model) : Z :=
live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).
Lemma vm_backing_used_split : ltac2:(TCodec.tc2 tcn__AsanAcct "H'R='D'K&S>r1%211&TB&SK%114&TE&TG&9'V=yR0%211&S4%11<%6231%811&S=%;221%?2=1%E3DA1pZFG1").
Proof. reflexivity. Qed.
Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
minv_nodup : List.NoDup (m_vm_materialized m);
minv_aligned : forall p, In p (m_vm_materialized m) ->
(bv_unsigned p mod page_size = 0)%Z;
minv_allowed : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
minv_lazy : forall p, In p (m_vm_materialized m) ->
page_in_ranges p (m_vm_lazy m) = true;
minv_budget : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.
Definition same_but_materialized (m m' : Model) : Prop :=
m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.
Lemma same_but_materialized_refl : ltac2:(TCodec.tc2 tcn__AsanAcct "5'R=&T6r1%2211pZF41").
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_but_materialized_trans : ltac2:(TCodec.tc2 tcn__AsanAcct "<'R=&T6r3r2%3221r5%5214p031p041pZN91pZL:1pZJ;1").
Proof.
unfold same_but_materialized. intros m1 m2 m3 -> ->.
destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.
Lemma with_vm_backing_same : ltac2:(TCodec.tc2 tcn__AsanAcct "@'R=':'V=yR0%211%411&T6r2&S@&S3%113r1%43215%7261p[291pZF?1").
Proof.
intros [fd [maps lazy mat] io fs proc lim tm] mat'. reflexivity.
Qed.
Lemma same_but_materialized_frame : ltac2:(TCodec.tc2 tcn__AsanAcct "SL'R=&T6r2r1%3221'C'D'R8&RF%117r3%311%63531'RA&S5%11=%216%;3421':'?'V=yR0%211%4211%611&S3%11H%21A%F3421'R;&RK%11M%21F%K3421'R9&RI%11Q2%21K%Q03421'R?&RN%11Q7%21Q0%Q53421'R<&RL%11Q<%21Q5%Q:3421'R@&S2%11QA%21Q:%Q?3421'R7%Q42Q11%Q611&RG%11QH%21QA%QF3421&R>%Q;2Q81%Q=11&RM%11QO%21QH%QM3421'R:&S0%11R4%21QM%R23421&O&RH%11R9%21R2%R73421'=%11QI&RJ%11R?%21R8%R=3421&S1%11RC%21R<%RA3821y8%R511%R811%=11&RO%11RK%21RD%RI3421&RE%11RO%21RH%RM3R=21'K&SK%11S4%21RM%S23421%S4261%S52;1%S62D1%S72I1%S82Q01%S92Q61%S:2Q<1%S;2QD1%S<2QL1%S=2R21%S>2R81%S?2R>1%S@2RD1%SA2RJ1%SB2S61%SC2S<1p0SE1pZHSJ1pZFSK1").
Proof.
intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm].
repeat split; reflexivity.
Qed.
Fixpoint A_pages (A : list (Z * Z)) : list Z :=
match A with
| [] => []
| iv :: r =>
map (fun i => (fst iv + page_size * Z.of_nat i)%Z)
(seq 0 (Z.to_nat ((snd iv - fst iv) / page_size)))
++ A_pages r
end.
Lemma Zmod0_multiple : ltac2:(TCodec.tc2 tcn__AsanAcct "A'K'D&TDr1&S=%3221z%63721'Er3&TE%1278%;3<31q\4=1%62>1p081pYF@1").
Proof.
intros a Ha. exists (a / page_size)%Z.
pose proof (Z.div_mod a page_size ltac:(unfold page_size; lia)) as Hdm.
rewrite Ha, Z.add_0_r in Hdm. exact Hdm.
Qed.
Lemma A_pages_length : ltac2:(TCodec.tc2 tcn__AsanAcct "H':'?'K%2211%411&SGr1%211'D&TE&TG&9&SFr2%211%42=1%611&S=%9221&SE%117%=3C31p0?1p2C1").
Proof.
induction A as [|[lo hi] A IH]; intros Hwf; [reflexivity|].
cbn [A_pages A_bytes fst snd]. inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst.
cbn [fst snd] in *.
rewrite length_app, length_map, length_seq, Nat2Z.inj_add, Z.mul_add_distr_r.
rewrite (IH Hwf').
destruct (Zmod0_multiple lo Hlo) as [qlo ->].
destruct (Zmod0_multiple hi Hhi) as [qhi ->].
replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
rewrite Z.div_mul by (unfold page_size; lia).
rewrite Z2Nat.id by (unfold page_size in Hle; lia).
reflexivity.
Qed.
Lemma A_pages_in : ltac2:(TCodec.tc2 tcn__AsanAcct "Q5':'?'K%2211%411'V=yR0%211&SGr2%211'D&TD&V?%1285&S=%4221z%73@21'6&T1r4r3%3221(@%>3621&T?%>2E6&SFr5%211%53M41p071p0?1p0H1p[NL1p2Q01").
Proof.
induction A as [|[lo hi] A IH]; intros p Hwf Hal Hpa; [discriminate|].
inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst. cbn [fst snd] in *.
cbn [A_pages fst snd]. apply in_or_app.
unfold page_allowedb in Hpa. cbn [existsb fst snd] in Hpa.
apply orb_true_iff in Hpa as [Hpa | Hpa].
- left. apply andb_true_iff in Hpa as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (Zmod0_multiple lo Hlo) as [qlo Eqlo].
destruct (Zmod0_multiple hi Hhi) as [qhi Eqhi].
destruct (Zmod0_multiple (bv_unsigned p) Hal) as [qp Eqp].
rewrite Eqp in *. rewrite Eqlo, Eqhi in *.
replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
rewrite Z.div_mul by (unfold page_size; lia).
apply in_map_iff. exists (Z.to_nat (qp - qlo)).
unfold page_size in *.
split.
+ rewrite Z2Nat.id by lia. lia.
+ apply in_seq. lia.
- right. apply IH; [exact Hwf' | exact Hal | exact Hpa].
Qed.
Lemma NoDup_map_bv_unsigned : ltac2:(TCodec.tc2 tcn__AsanAcct "A':'V=yR0%211%411'T@r1%2241'K&I&V?%119r2%44:521%9261p081pZ><1").
Proof.
intros l Hnd. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor; [|exact IH].
intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
apply bv_eq in Hy. subst y. exact (Hx Hiny).
Qed.
Theorem allowed_pages_bound : ltac2:(TCodec.tc2 tcn__AsanAcct "QG':'?'K%2211%411'V=yR0%211%811&SGr2%211'T@%1263&T?r1r4%33:21'D&TD&V?%12?;&S=%4221z%73G21p091p[ND1r5%?3F>1'6&T1r7%221G(@%A3521p071p[NN1&TC&TE&TG&9%12Q3>%311%521F&SEr6%211%:241p0<1p0G1p0Q61p0Q91p\0Q=1p2QB1").
Proof.
intros A pages Hwf Hnd Hal Hpa.
rewrite <- (A_pages_length A Hwf).
assert (Hlen : (length pages <= length (A_pages A))%nat).
{ rewrite <- (length_map bv_unsigned pages).
apply NoDup_incl_length.
- apply NoDup_map_bv_unsigned. exact Hnd.
- intros z Hz. apply in_map_iff in Hz as (p & <- & Hp).
apply A_pages_in; [exact Hwf | exact (Hal p Hp) | exact (Hpa p Hp)]. }
unfold page_size. lia.
Qed.
Lemma two64_as_pages : ltac2:(TCodec.tc2 tcn__AsanAcct "<'D'K&TH+2+R0%3221&TE&S=+QD%7261%4231%;3:61").
Proof. reflexivity. Qed.
Lemma page_base_woff : ltac2:(TCodec.tc2 tcn__AsanAcct "F'V=yR0%211';'D&S8&T9r2r1%3221%511&S9&TB&V?%12=7&TG%118%5231%711%?3A91pZ<A1pYFC1").
Proof.
intros a k. unfold page_base, woff, page_base_of.
set (z := (bv_unsigned a + Z.of_nat k)%Z).
pose proof (bv_unsigned_in_range 64 a) as Ha.
assert (Hz : (0 <= z)%Z) by (unfold z; lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite !two64_as_pages.
set (r := (z mod (page_size * 2 ^ 52))%Z).
assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
pose proof (Z.div_mod z (page_size * 2 ^ 52) ltac:(lia)) as Hdm.
fold r in Hdm.
set (q := (z / (page_size * 2 ^ 52))%Z) in Hdm.
assert (Hfl : (z / page_size * page_size = page_size * 2 ^ 52 * q + r / page_size * page_size)%Z).
{ rewrite Hdm at 1.
replace (page_size * 2 ^ 52 * q + r)%Z with (r + (2 ^ 52 * q) * page_size)%Z by lia.
rewrite Z.div_add by lia. lia. }
rewrite Hfl.
replace (page_size * 2 ^ 52 * q + r / page_size * page_size)%Z
with (r / page_size * page_size + q * (page_size * 2 ^ 52))%Z by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma page_base_of_aligned : ltac2:(TCodec.tc2 tcn__AsanAcct ">'K'D&TD&V?yR0&S9r1%211%5241&S=%8221z%;3<21p]:=1").
Proof.
intros z. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64)%Z. rewrite two64_as_pages.
rewrite (Z.mul_comm (z / page_size) page_size).
rewrite Zmult_mod_distr_l.
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma page_insert_nodup : ltac2:(TCodec.tc2 tcn__AsanAcct "@'V=yR0%211':%112'T@r1%2251&S;r3r2%3221%72:1p061p\0:1p[N=1").
Proof.
intros p pages Hnd. unfold page_insert.
destruct (page_mem p pages) eqn:Hm; [exact Hnd|].
constructor; [|exact Hnd].
intros Hin. unfold page_mem in Hm.
assert (Ht : existsb (bv_eqb p) pages = true).
{ apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
rewrite Ht in Hm. discriminate.
Qed.
Lemma page_mem_false_not_in : ltac2:(TCodec.tc2 tcn__AsanAcct "E'V=yR0%211':%112'D'6&S<r2r1%3221(8%73621&F&T?r3%23>18%411p061p\0?1p[NB1").
Proof.
intros p pages Hm Hin. unfold page_mem in Hm.
assert (Ht : existsb (bv_eqb p) pages = true).
{ apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
rewrite Ht in Hm. discriminate.
Qed.
Lemma access_pages_acc_nodup : ltac2:(TCodec.tc2 tcn__AsanAcct "D';'K':'V=yR0%211%411'T@r1%2241&RBr3r4r2%43321%82:1p071p\0;1pYLA1p[JC1").
Proof.
induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
apply IH. apply page_insert_nodup. exact Hnd.
Qed.
Lemma accesses_pages_nodup : ltac2:(TCodec.tc2 tcn__AsanAcct "D':'?'V=yR0%211';%5221%711%814'T@r1%2271&RCr3r2%3221%72<1p061p\0:1pYH<1").
Proof.
induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.
Lemma page_insert_in : ltac2:(TCodec.tc2 tcn__AsanAcct "F'V=yR0%211':%112&T?r3&S;r2r1%3221%63951'G'Dr4%23=19%;3>28%5221p071p\0?1p\4B1p[NC1").
Proof.
intros p q pages Hin. unfold page_insert in Hin.
destruct (page_mem q pages); [right; exact Hin|].
destruct Hin as [Hqp | Hin]; [left; symmetry; exact Hqp | right; exact Hin].
Qed.
Lemma access_pages_acc_in : ltac2:(TCodec.tc2 tcn__AsanAcct "Q8';'K':'V=yR0%211%411&T?r1&RBr3r4r2%43321%73961'G%93;46'E'C&Hr6%22=1'D&S9&TBr5&TG%11C%4231%611%83ID1%=2:1qZ<Q01%@2Q11%C2B1p0E1p[NO1p\0O1pYLQ51p[JQ71").
Proof.
induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p Hin.
- left; exact Hin.
- destruct (IH (base + 1)%Z _ p Hin) as [Hin' | (k & Hk & ->)].
+ destruct (page_insert_in _ _ _ Hin') as [-> | Hin''].
* right. exists 0%nat. split; [lia|]. f_equal. lia.
* left; exact Hin''.
+ right. exists (S k). split; [lia|]. f_equal. lia.
Qed.
Lemma accesses_pages_in : ltac2:(TCodec.tc2 tcn__AsanAcct "QB':'?'V=yR0%211';%5221%711%814&T?r1&RCr3r2%3221%63;51'G%83=45'E'C(>%14A@98r7%>3A21&H%12?<'Dr5&S9&TB&V?%12LC&TG%11G%5231%711%:3Q091%B2<1%C2?1qZ<Q21%F2Q31q[JQ41%H2Q51qYFQ71%J2Q81%M2L1p0O1p[NQ;1p\0Q81pYHQ:1").
Proof.
induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p Hin.
- left; exact Hin.
- destruct (IH _ p Hin) as [Hin' | (a' & n' & k & Hin' & Hk & Hp)].
+ destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin') as [Hp | (k & Hk & Hp)].
* left; exact Hp.
* right. exists a, n, k. split; [left; reflexivity | split; assumption].
+ right. exists a', n', k. split; [right; exact Hin' | split; assumption].
Qed.
Lemma new_pages_props : ltac2:(TCodec.tc2 tcn__AsanAcct "R:'V=yR0%211'6p021':'?'K%2211%411%4288%611%71:';%82<1%:11&SMr5r3r4%43321&T3r6r2%3221&S7%13978'C'T@r1%22L1&T?%13N39&Fr7%43Q1<1%311p051p[NQ41'D&TD&V?%12Q9C&S=%4221z%73Q721p0?1p[NQ>1&S:r8%22L1(@%>3QB21p0F1p[NQE1&T1r9%221Q3%D3QH17p0L1p[NQK1%Q3271%Q42?1%Q52J1%Q62Q31t[LQFQ81p0Q;1p0Q@1p\8QF1p[0QJ1pZDQL1p2QO1pQJR51").
Proof.
intros H A lazy mat ranges Hcov Hav new.
assert (Hchar : forall p, In p new ->
page_in_ranges p lazy = true /\ page_mem p mat = false
/\ exists a n k, In (a, n) ranges /\ (k < n)%nat
/\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z).
{ intros p Hin. unfold new, newly_materialized_pages in Hin.
apply filter_In in Hin as [Hin Hf]. apply andb_true_iff in Hf as [Hl Hm].
split; [exact Hl|]. split; [destruct (page_mem p mat); [discriminate | reflexivity]|].
destruct (accesses_pages_in ranges [] p Hin) as [[] | Hex]. exact Hex. }
split; [|split; [|split; [|split]]].
- unfold new, newly_materialized_pages. apply NoDup_filter.
apply accesses_pages_nodup. constructor.
- intros p Hp. destruct (Hchar p Hp) as (_ & Hm & _). apply page_mem_false_not_in. exact Hm.
- intros p Hp. destruct (Hchar p Hp) as (_ & _ & a & n & k & _ & _ & ->).
apply page_base_of_aligned.
- intros p Hp. destruct (Hchar p Hp) as (Hl & _). exact Hl.
- intros p Hp. destruct (Hchar p Hp) as (Hl & _ & a & n & k & Hin & Hk & Ep).
pose proof (Hav a n Hin k Hk) as Hw.
rewrite <- page_base_woff in Ep. rewrite Ep in Hl |- *.
exact (Hcov (woff a k) Hl Hw).
Qed.
Lemma m_vm_materialized_wvb : ltac2:(TCodec.tc2 tcn__AsanAcct "E':'?'V=yR0%211%4211%611%713'R='D&S4&S@r3r2r1%43321%611%83:14pZF:1pYD<1pZ>>1").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : ltac2:(TCodec.tc2 tcn__AsanAcct "E':'?'V=yR0%211%4211%611%713'R='D&S3&S@r3r2r1%43321%611%83;15pZF:1pYD<1pZ>>1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : ltac2:(TCodec.tc2 tcn__AsanAcct "G':'?'V=yR0%211%4211%611%713'R='D'RA&S5&S@r3r2r1%43321%611%713%:3921pZF<1pYD>1pZ>@1").
Proof. reflexivity. Qed.
Lemma m_halted_wvb : ltac2:(TCodec.tc2 tcn__AsanAcct "H':'?'V=yR0%211%4211%611%713'R='D'=%117&RJ&S@r3r2r1%43321%611%713%;3921pZF=1pYD?1pZ>A1").
Proof. reflexivity. Qed.
Lemma eager_used_wvb : ltac2:(TCodec.tc2 tcn__AsanAcct "D':'V=yR0%211%411'R='D'K&SK&S@&S3r1%211r2%53213%711%815%;3:21pZF=1pYD?1").
Proof. reflexivity. Qed.
Lemma with_vm_backing_id : ltac2:(TCodec.tc2 tcn__AsanAcct ";'R='D&S@&S3r1%211&S4%113%63314%83915pZF:1").
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma MInv_wvb : ltac2:(TCodec.tc2 tcn__AsanAcct "R8':'?'K%2211%411'R='V=yR0%211%911'T@r1%2241&T?r3%23741'D&TD&V?r2%22=1&S=%5221z%83F21p0:1p[NB1r4%?3DA1'6&T1r7%221=(@%B3521p071p[NL1r5%I3NK1&S:&S3%11:%32G1%K3>1:p061p[NQ51&TC&TB&SKr6%211&SE%11E%6231&S?&S5%117%311%<251'SIr8&S@%13E=O%4231p061p0D1p0N1p0Q91p0QH1pYDQL1pZFR11p2R31").
Proof.
intros A m X H1 H2 H3 H4 H5. constructor;
rewrite ?m_vm_materialized_wvb, ?m_vm_lazy_wvb, ?m_vmmaps_wvb, ?eager_used_wvb;
assumption.
Qed.
Theorem materialize_restricted : ltac2:(TCodec.tc2 tcn__AsanAcct "QJ'V=yR0%211'6p021':'?'K%2211%411'R=';%62:1%811&SMr4&S3r2%211r3%63521&SG%117'SIr5%221:&T3r7%221='E%I1L'C'D'=%11H&S6r6%22:1(4&S@%H1=r1%3321?%52Q11%<3:71r8%G214%@231q[2B1%D2C1p0F1p0J1p0N1p0Q11p\8Q91pZFQ=1p2Q?1pQJQE1").
Proof.
intros H A m ranges Hcov Hwf [Hnd Hal Hpa Hlz Hbud] Hav.
destruct (new_pages_props H A (m_vm_lazy m) (m_vm_materialized m) ranges Hcov Hav)
as (Nnd & Nfresh & Nal & Nlz & Npa).
unfold materialize_model_accesses, materialize_accesses.
set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges) in *.
assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m)).
{ apply NoDup_app; [exact Nnd | exact Hnd | exact Nfresh]. }
assert (Happ_al : forall p, In p (new ++ m_vm_materialized m) ->
(bv_unsigned p mod page_size = 0)%Z).
{ intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nal p Hp) | exact (Hal p Hp)]. }
assert (Happ_pa : forall p, In p (new ++ m_vm_materialized m) -> page_allowedb A p = true).
{ intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Npa p Hp) | exact (Hpa p Hp)]. }
assert (Happ_lz : forall p, In p (new ++ m_vm_materialized m) ->
page_in_ranges p (m_vm_lazy m) = true).
{ intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nlz p Hp) | exact (Hlz p Hp)]. }
pose proof (allowed_pages_bound A (new ++ m_vm_materialized m) Hwf Happ_nd Happ_al Happ_pa)
as Hbound.
rewrite length_app, Nat2Z.inj_add in Hbound.
destruct new as [|p0 new'] eqn:Enew.
- exists (m_vm_materialized m). split; [reflexivity|].
apply MInv_wvb; assumption.
- rewrite vm_backing_used_split.
replace (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size
+ Z.of_nat (length (p0 :: new')) * page_size
<=? vm_limit (m_vmmaps m))%Z with true.
2:{ symmetry. apply Z.leb_le. unfold page_size in *. lia. }
exists ((p0 :: new') ++ m_vm_materialized m). split; [reflexivity|].
apply MInv_wvb; assumption.
Qed.
Section Nodes.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.
Definition node_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep segs c (evs i) (SNext (nx i)))
/\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).
Theorem mi_account_step_restricted : ltac2:(TCodec.tc2 tcn__AsanAcct "R7':'?'K%2211%411'QA'R=&SMvL&S3r1%211r4%63521&SGr5%211'SIr6r3%3221'D'Q@%11B&QMvV:&T5%12C9%4231(Q3%12I?%:3831'E'V=yR0%211%Q411'C%Q52Q1Q0%A11&R3r8%23A1H(>&T8&QE%115r7%43Q821&S@%Q91Q0%231Q9Q1%94Q?Q>41%H2?1%Q13?<1r9%Q7215&SL%12QB;%F231%G261q[2I1%N2J1p0Q01p0Q<1p0QA1p0QE1p[8QM1p[FQO1p[@R01p2R21").
Proof.
intros A ms msr' model Hcov Hwf Hinv Hs.
destruct (step_restrict_sound segs H HH Hwx ms msr' Hs) as (rep & Hsa & Hv & Hrs & Hcl & _).
destruct (materialize_restricted H A model (accessed_ranges _ rep) Hcov Hwf Hinv Hrs)
as (mat' & Hmat & Hinv').
exists mat'. unfold mi_account_step. rewrite Hsa, Hmat, Hv.
split; [reflexivity | split; [exact Hinv' | exact Hcl]].
Qed.
Lemma sstep_instr_det : ltac2:(TCodec.tc2 tcn__AsanAcct "QI'QA'R=':'RD%211'R6'D'='V=yR0%211%411&QJr6%211(1%116%;3631'Q@'?%12DC%311&R3vV:r7%3321<(Q3(>r5r4%34NM21%52;1%J3;71'R5(R4r8%221<r3%54?291'C(<%11Q6%Q43Q6>1(R2%:2DO%211%Q83Q9A1%8251p0:1p0A1p0Q11p\HQ>1pZ2Q@1p[<QD1p[DQF1p[8QF1p[@QH1").
Proof.
intros ms model ms1 model1 e st Hsvc Hacc Hss.
inversion Hss; subst;
match goal with
| Hp : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in Hp; discriminate
| Ha : mi_account_step segs ms model = _ |- _ =>
rewrite Hacc in Ha; try discriminate; injection Ha as <- <-; split; reflexivity
end.
Qed.
Theorem node_instr_restricted : ltac2:(TCodec.tc2 tcn__AsanAcct "S3':'?'K%2211%411'QA'R=&SMvL&S3r1%211r4%63521&SGr5%211'SIr6r3%3221'D'='V=yR0%211%411&RJ%11@(1%115%:3531&QJr7%211%>3915'Q@%11Q0&QMvV:&T5r8%22Q21%5241(Q3%12Q8<%I3931'E'Cr;%Q121Q8&T6%12;Q:&SLr9%22Q?1%QG2QCQB%E11&R3r:%23E1C(>&T8&QE%115%33QI1;%54QMQL1QH%G2;1%Q?3;81&SJ(R4%12<N'A(<'RD%211q041%>1L%@3R61Cr2%:221q091%=4;:61%Q32?1%Q42M1%Q52Q11%Q62Q41q[:RA1%Q92RB1p0Q;1p0QG1p0QL1p0R81p0R=1p0RA1p[8RI1p[FRK1p[@RL1p2RN1").
Proof.
intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs.
destruct (mi_account_step_restricted A ms msr' model Hcov Hwf Hinv Hs)
as (mat' & Hacc & Hinv' & Hcl).
exists (with_vm_backing (m_vm_lazy model) mat' model).
split; [exact Hinv'|]. split; [apply with_vm_backing_same|]. split; [exact Hcl|].
split; [exact Hacc|].
split.
- intros []. apply sstep_instr; [exact Hh | exact Hsvc | exact Hacc].
- intros e st Hss. exists tt.
exact (sstep_instr_det ms model _ _ e st Hsvc Hacc Hss).
Qed.
Lemma step_hclean : ltac2:(TCodec.tc2 tcn__AsanAcct "D'QA&SLvLr2%3221'D'Q@%117&QMvV:r3%3221(Q3%12=:%93731%>2=5p021p0=1p[BB1p[@C1").
Proof.
intros ms ms' Hc Hs. rewrite <- (hclean_restrict_id H ms Hc) in Hs.
destruct (step_restrict_sound segs H HH Hwx ms ms' Hs) as (rep & _ & _ & _ & Hcl & _).
exact Hcl.
Qed.
Lemma msteps_hclean : ltac2:(TCodec.tc2 tcn__AsanAcct ">'QA'T<vV:r2r1%43321&SLvLr3%3221p011p061p[B<1p[@=1").
Proof.
intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; intros Hc.
- exact Hc.
- apply IH. exact (step_hclean ms ms1 Hc Hstep).
Qed.
Lemma unrestrict_munrestrict : ltac2:(TCodec.tc2 tcn__AsanAcct "G'V=yR0%211'=y8%511%311p051'QA'D&T8vL&T0r3r2%33421r1%73621%83752%:3;21p[B<1pZ:>1pZ4?1").
Proof.
intros f g ms'. unfold unrestrict. f_equal.
apply functional_extensionality. intro x. unfold munrestrict.
destruct (H x); reflexivity.
Qed.
Variable P : config -> Prop.
Hypothesis P_silent1 : forall c c',
ms_svc_pending (cfg_ms c) = None ->
node_ok c unit (fun _ => []) (fun _ => c') -> P c' -> P c.
Theorem rz_step_restricted : ltac2:(TCodec.tc2 tcn__AsanAcct "R?':'?'K%2211%411'QA'R=&SMvL&S3r1%211r4%63521&SGr5%211'SIr6r3%3221'D'='V=yR0%211%411&RJ%11@(1%115%:3531&QJr7%211%>3915'Q@%11Q0&QMvV:&T5r8%22Q21%5241(Q3%12Q8<%I3931r;%O21Q6&T6r9r2%3221vSD(R4&T8&QEr<%211%43QC1<%621Q9%811p0:1p0?1p[:QJ1r:%<21I%>11p041p0G1p0Q31p0Q81p0QD1p0QI1p0QM1p[8R51p[FR71p[@R81p2R:1").
Proof.
intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs Hk.
destruct (node_instr_restricted A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
as (model' & Hinv' & Hsame & _ & _ & Hnode).
exact (P_silent1 (mkCfg ms model) _ Hsvc Hnode (Hk model' Hinv' Hsame)).
Qed.
Theorem rz_msteps_restricted : ltac2:(TCodec.tc2 tcn__AsanAcct "R7':'?'K%2211%411'QA'T<vV:r2r1%43321'R='Dr5&T5vL%2218%53<41&SM&S3%11<r7%43721&SGr8%211'SIr9r4%3221'='V=yR0%211%411&RJ%11G(1%115%K3531r<%?21Q0&T6%12CQ3vSD(R4&T8&QEr:%211%43Q31:r3%7221%911p0;1p0>1p[:Q=1%<2Q1Q4%>11p031p0E1p0Q01p0Q51p0Q91p0Q?1p[8QF1p[@QM1p0QI1p[FQO1p[HR01p2R21").
Proof.
intros A msr0 msr' Hms.
induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH];
intros ms model -> Hcov Hwf Hinv Hh Hk.
- specialize (Hk model Hinv (same_but_materialized_refl model)).
rewrite unrestrict_restrict in Hk. exact Hk.
- rewrite restrict_svc_pending in Hsvc.
destruct (node_instr_restricted A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
as (model1 & Hinv1 & Hsame1 & Hcl1 & _ & Hnode).
apply (P_silent1 (mkCfg ms model) _ Hsvc Hnode).
pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
apply (IH (unrestrict H (ms_mem ms) msr1) model1).
+ symmetry. apply restrict_unrestrict_clean. exact Hcl1.
+ replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
+ exact Hwf.
+ exact Hinv1.
+ replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
+ intros model' Hinv' Hsame'.
rewrite unrestrict_mem, unrestrict_munrestrict.
apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame')].
Qed.
Theorem rz_msteps_restricted' : ltac2:(TCodec.tc2 tcn__AsanAcct "R9':'?'K%2211%411'QA'R=&SMvL&S3r1%211r4%63521&SGr5%211'SIr6r3%3221'D'='V=yR0%211%411&RJ%11@(1%115%:3531'T<vV:&T5r7%22L1%5341Cr:%F21M&T6r8r2%3221&SL%12Q57vSD(R4&T8&QEr<%211r;%53Q=21%721Q:%911p0;1p0>1p0C1p[:QE1r9%>21J%@11p041p0K1p0Q21p0Q>1p0QC1p0QG1p[8QO1p[FR11p[@R21p2R41").
Proof.
intros A ms msr' model Hcov Hwf Hinv Hh Hms Hk.
pose proof (msteps_hclean _ _ Hms (restrict_hclean H ms)) as Hcl.
apply (rz_msteps_restricted A (restrict H ms) msr' Hms ms model eq_refl Hcov Hwf Hinv Hh).
intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' Hcl).
Qed.
End Nodes.
Lemma materialize_model_accesses_nil : ltac2:(TCodec.tc2 tcn__AsanAcct "C'R='D'=%113&S6r1(<'?'V=yR0%211';%5221%711%:291(4%12@;%@3>31pZFB1").
Proof.
intros m. unfold materialize_model_accesses, materialize_accesses.
unfold newly_materialized_pages. cbn [accesses_pages List.filter].
rewrite with_vm_backing_id. reflexivity.
Qed.
Definition materialized_succ (m : Model) (accs : list (word * nat)) : Model :=
match materialize_model_accesses m accs with
| Some m' => m'
| None => m
end.
Section SyscallNode.
Variable segs : list Segment.
Variable H : word -> bool.
Theorem node_syscall_restricted :
forall A ms model x8 (I : Type)
(eff : I -> SyscallEffect) (mdl : I -> Model) (evs : I -> list event),
A_wf A ->
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall i, syscall_spec (sys_input segs ms x8) model (Ok (eff i) (mdl i) (evs i))) ->
(forall r, syscall_spec (sys_input segs ms x8) model r ->
exists i, r = Ok (eff i) (mdl i) (evs i)) ->
(forall i, m_halted (mdl i) = None) ->
(forall i, lazy_cover H (m_vm_lazy (mdl i)) A) ->
(forall i, MInv A (mdl i)) ->
(forall i, ranges_avoid H (syscall_effect_accesses (eff i))) ->
(forall i, MInv A (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))
/\ same_but_materialized (mdl i)
(materialized_succ (mdl i) (syscall_effect_accesses (eff i))))
/\ node_ok segs (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (eff i)))
(materialized_succ (mdl i) (syscall_effect_accesses (eff i)))).
Proof.
intros A ms model x8 I eff mdl evs Hwf Hh Hsvc Hsound Hcompl Hnh Hcov Hinv Hav.
assert (Hmat : forall i, exists mat',
materialize_model_accesses (mdl i) (syscall_effect_accesses (eff i))
= Some (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))
/\ MInv A (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))).
{ intros i. exact (materialize_restricted H A (mdl i) _ (Hcov i) Hwf (Hinv i) (Hav i)). }
split.
- intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
unfold materialized_succ. rewrite Hm. split; [exact Hinv' | apply with_vm_backing_same].
- split.
+ intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
unfold materialized_succ. rewrite Hm.
eapply sstep_syscall; [exact Hh | exact Hsvc | exact (Hsound i) | exact (Hnh i) | exact Hm].
+ intros e st Hss. inversion Hss; subst;
match goal with
| Hp : ms_svc_pending ms = None |- _ => rewrite Hsvc in Hp; discriminate
| Hp : ms_svc_pending ms = Some ?x |- _ =>
rewrite Hsvc in Hp; injection Hp as <-
end;
match goal with
| Hsp : syscall_spec _ _ ?r |- _ =>
destruct (Hcompl _ Hsp) as [i Ei]; try discriminate Ei;
injection Ei as -> -> ->
end.
*
exists i. split; [reflexivity|].
unfold materialized_succ.
match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite Hm end.
reflexivity.
*
destruct (Hmat i) as (mat' & Hm & _).
match goal with Hn : materialize_model_accesses _ _ = None |- _ => rewrite Hm in Hn; discriminate end.
*
match goal with Hc : m_halted (mdl i) = Some _ |- _ => rewrite (Hnh i) in Hc; discriminate end.
*
match goal with Hk : m_killed (mdl i) = Some _ |- _ =>
rewrite (m_killed_of_m_halted_none _ (Hnh i)) in Hk; discriminate end.
Qed.
End SyscallNode.
Definition mkH (L : list (word * word)) (A : list (Z * Z)) : word -> bool :=
fun a => page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a)).
Lemma page_in_ranges_incl : ltac2:(TCodec.tc2 tcn__AsanAcct "K'V=yR0%211':'?%1233%311&TAr2r1%33521'D'6&S:r4r3%3221(@%73621r5%7215%:3914p041p0=1pQNB1pZ>C1p[NH1").
Proof.
intros p l L Hincl Hp. unfold page_in_ranges in *.
apply existsb_exists in Hp as (r & Hin & Hr).
apply existsb_exists. exists r. split; [exact (Hincl r Hin) | exact Hr].
Qed.
Lemma lazy_cover_mkH : ltac2:(TCodec.tc2 tcn__AsanAcct "H':'?'V=yR0%211%4211%611'K%7211%911&TAr1r3%33821&SM&SNr4%2215r2%53217p071pZD?1p2=1pQNA1").
Proof.
intros L A lazy Hincl w Hl Hw. unfold mkH in Hw.
rewrite (page_in_ranges_incl _ _ _ Hincl Hl) in Hw. cbn in Hw.
destruct (page_allowedb A (page_base w)); [reflexivity | discriminate].
Qed.
Definition seg_top (seg : Segment) : Z :=
(Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Definition wx_segs_nowrap_b (segs : list Segment) : bool :=
forallb (fun seg => negb (seg_executable seg && seg_writable seg)
|| (seg_top seg <=? 2 ^ 64)%Z) segs.
Lemma wx_segs_nowrap_of_b : ltac2:(TCodec.tc2 tcn__AsanAcct "?':'Q0%211'D'6&T;r1%211(@%63521&T:r2%211p041p\F<1").
Proof.
intros segs Hb seg Hin Hwx. unfold wx_segs_nowrap_b in Hb.
rewrite forallb_forall in Hb. specialize (Hb seg Hin). rewrite Hwx in Hb. cbn in Hb.
apply Z.leb_le in Hb. exact Hb.
Qed.
Definition segs_below_b (segs : list Segment) (top : Z) : bool :=
forallb (fun seg => (seg_top seg <=? top)%Z) segs.
Lemma find_segment1_none_above : ltac2:(TCodec.tc2 tcn__AsanAcct "L':'Q0%211'K'D'6&T7r3r2%3221(@%73621&TC%1265'=%11>&Q>r5+1%332<1(1%11D%B3731p0:1p0=1p]8F1p]4G1p\FI1").
Proof.
induction segs as [|s l IH]; intros top x Hb Hx; [reflexivity|].
cbn [segs_below_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
apply Z.leb_le in Hs. unfold seg_top in Hs.
cbn [find_segment].
replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z
with false.
- exact (IH top x Hl Hx).
- symmetry. apply andb_false_iff. right. apply Z.leb_gt. lia.
Qed.
Lemma H_off_segments_above : ltac2:(TCodec.tc2 tcn__AsanAcct "Q2':'Q0%211'V=yR0%211'6p021'K'D&T7r3r1%3221(@%63921r4%115%93<14&TC&V?r2%22B1%4271p061pYFD1&SHr5%221<p041p0?1p]4G1pQJI1p\FO1").
Proof.
intros segs H top Hb Ha a HHa. exact (find_segment1_none_above segs top _ Hb (Ha a HHa)).
Qed.
Definition ranges_from_b (L : list (word * word)) (top : Z) : bool :=
forallb (fun r => (top <=? bv_unsigned (fst r))%Z) L.
Lemma page_base_le : ltac2:(TCodec.tc2 tcn__AsanAcct "<'V=yR0%211&TC&V?&S8r1%211%4271%5283%7221pYF91").
Proof.
intros a. unfold page_base, page_base_of. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 64 a) as Ha.
pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hdm.
pose proof (Z.mod_pos_bound (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hmb.
assert (Hq : (0 <= bv_unsigned a / page_size)%Z)
by (apply Z.div_pos; unfold page_size in *; lia).
set (q := (bv_unsigned a / page_size)%Z) in *.
change (bv_modulus 64) with (2 ^ 64)%Z in *. unfold page_size in *.
rewrite bv_wrap_small; [lia|].
change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.
Lemma mkH_above : ltac2:(TCodec.tc2 tcn__AsanAcct "Q1':'?'V=yR0%211%4211%611'K%7211%911'D'6&T4r4r2%3221(@%73621&SNr5%23176%;3:15&TC&V?r3%22F1%42=1p061p0;1pYFI1p]4G1p2F1pQNJ1").
Proof.
intros L A top a Hb Ha. unfold mkH in Ha. apply andb_true_iff in Ha as [Hp _].
unfold page_in_ranges in Hp. apply existsb_exists in Hp as ([lo sz] & Hin & Hr).
cbn [fst snd] in Hr. apply andb_true_iff in Hr as [H1 _]. apply Z.leb_le in H1.
unfold ranges_from_b in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Hin).
cbn [fst] in Hb. apply Z.leb_le in Hb.
pose proof (page_base_le a). lia.
Qed.
Corollary H_off_segments_mkH : ltac2:(TCodec.tc2 tcn__AsanAcct "Q4':'Q0%211'?'V=yR0%211%4211%811'K%7211%;11'D'6&T7r4r1%3221(@%73621&T4r2%2271%;3:15&SHr6&SNr5%221=%5241p071p0<1p]4G1p2F1pQNJ1p\FQ11").
Proof.
intros segs L A top Hs HL.
apply (H_off_segments_above segs (mkH L A) top Hs).
intros a Ha. exact (mkH_above L A top a HL Ha).
Qed.
Lemma MInv_intro_empty : ltac2:(TCodec.tc2 tcn__AsanAcct "Q6':'?'K%2211%411'R='D'V=yR0%211%:11&S4r1%211(<%116%:3631&TC&TB&SKr2%211&SEr3%211%7241&S?&S5%118%311%=251'SIr4%221:p041p0C1pZFO1p2Q11").
Proof.
intros A m He Hb. constructor; rewrite ?He;
[constructor | intros p Hp; destruct Hp | intros p Hp; destruct Hp
| intros p Hp; destruct Hp | exact Hb].
Qed.
Lemma MInv_transport : ltac2:(TCodec.tc2 tcn__AsanAcct "QA':'?'K%2211%411'R='SIr3r2%3221'D'V=yR0%211%>11&S4%118%21:%83421%B266%D11&S3%11?r4%311%?3531&TC&TB&SK%116&SEr6%211%6241&S?&S5%11=%311%<251r7r5%Q3221p041p0B1p0J1p0Q41pZHQ91pZFQ:1p2Q<1").
Proof.
intros A m m' [H1 H2 H3 H4 H5] Hm Hl Hb. constructor; rewrite ?Hm, ?Hl; assumption.
Qed.
End FPX_1.
